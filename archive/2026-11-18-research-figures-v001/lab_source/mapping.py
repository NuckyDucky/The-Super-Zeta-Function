"""Precision-preserving viewport coordinates; display position and magnification are independent."""
from functools import lru_cache
import math
import mpmath
import numpy as np

MAPPINGS={'cartesian','log','fold','kepler'}
DEFAULT_VIEWPORT=dict(mapping='cartesian',center_re='0',center_im='0.625',width='0.28',height='0.24',
    depth='-3',depth_span='2',sign=1,lateral_power='0',u_re='dottie',u_im='0')

@lru_cache(maxsize=24)
def special_constants(digits):
    m=mpmath.mp.clone();m.dps=digits+15
    d=m.findroot(lambda x:m.cos(x)-x,m.mpf('.74'));s=m.sin(d);y=m.exp(-s)
    c=4*m.pi**2*y/(1+s)
    return {k:m.nstr(v,digits+8) for k,v in dict(d=d,s=s,ystar=y,Cstar=c).items()}

def clean_viewport(viewport):
    v={**DEFAULT_VIEWPORT,**(viewport or {})}
    if v['mapping'] not in MAPPINGS:raise ValueError('Unknown coordinate mapping.')
    for k in ['center_re','center_im','width','height','depth','depth_span','lateral_power','u_re','u_im']:
        v[k]=str(v[k])
        if len(v[k])>2200:raise ValueError('Coordinate text exceeds 2200 characters.')
    v['sign']=-1 if int(v.get('sign',1))<0 else 1
    return v

def working_digits(v):
    m=mpmath.mp.clone();m.dps=40
    estimates=[80]
    for name in ['width','height']:
        value=m.mpf(v[name])
        if not m.isfinite(value) or value<=0:raise ValueError('Viewport spans must be positive finite values.')
        estimates.append(int(max(0,-m.log10(value)))+70)
    if v['mapping'] in ['log','fold']:
        depth=m.mpf(v['depth']);span=m.mpf(v['depth_span'])
        if not m.isfinite(depth) or abs(depth)>10000 or not 0<span<=1000:
            raise ValueError('Depth exponent must be finite within ±10000; depth span in (0,1000].')
        estimates.append(int(abs(depth)* (2 if v['mapping']=='fold' else 1)+span+70))
    # Planning/navigation touch only a few points. Use the full guard budget so
    # large centers with fine offsets and very small depth spans remain distinct.
    return 600

def build_mapper(viewport,digits=80):
    v=clean_viewport(viewport);m=mpmath.mp.clone();m.dps=max(35,int(digits)+18)
    vals={k:m.mpf(v[k]) for k in ['center_re','center_im','width','height','depth','depth_span','lateral_power','u_im']}
    for value in vals.values():
        if not m.isfinite(value):raise ValueError('Coordinates must be finite.')
    for k in ['width','height','depth_span']:
        if vals[k]<=0:raise ValueError('Coordinate spans must be positive.')
    c={k:m.mpf(x) for k,x in special_constants(max(40,int(digits)+8)).items()}
    vals['u_re']=c['d'] if v['u_re']=='dottie' else m.mpf(v['u_re'])
    if not m.isfinite(vals['u_re']):raise ValueError('Kepler coordinates must be finite.')
    mode=v['mapping']
    def point(x,y):
        x=m.mpf(x);y=m.mpf(y)
        if mode=='cartesian':return m.mpc(vals['center_re']+vals['width']*x,vals['center_im']+vals['height']*y),None
        if mode=='kepler':
            u=m.mpc(vals['u_re']+vals['width']*x,vals['u_im']+vals['height']*y)
            co=m.cos(u)
            if not co:raise ValueError('The selected Kepler coordinate is a cosine pole.')
            a=u*m.tan(u)
            if abs(m.re(a))>100000:raise ValueError('Kepler parameter exceeds the coordinate evaluation budget.')
            return m.j*u/co*m.exp(-a),u
        depth=vals['depth']+vals['depth_span']*y
        if mode=='log':
            delta=v['sign']*m.power(10,depth)
            lateral=m.power(10,vals['lateral_power']*(depth-vals['depth']))
        else:
            scale=m.power(10,depth)
            delta=v['sign']*c['Cstar']/scale**2
            lateral=m.power(10,vals['lateral_power']*(vals['depth']-depth))
        return m.mpc(vals['center_re']+vals['width']*x*lateral,c['ystar']+delta),None
    return m,point,vals,c

def precision_plan(viewport,width,height,requested='auto'):
    v=clean_viewport(viewport);wd=working_digits(v)
    m,point,_,_=build_mapper(v,wd)
    differences=[];magnitudes=[m.mpf(1)];float_safe=True
    for x,y in [('0','0'),('-.49','-.49'),('.49','.49'),('-.49','.49'),('.49','-.49')]:
        z,_=point(x,y);zx,_=point(m.mpf(x)+1/max(2,width),y);zy,_=point(x,m.mpf(y)+1/max(2,height))
        for value in [z.real,z.imag,zx.real,zx.imag,zy.real,zy.imag]:
            try:
                f=float(value)
                if not math.isfinite(f) or (value!=0 and f==0):float_safe=False
            except (ValueError,OverflowError):float_safe=False
        for diff in [abs(zx-z),abs(zy-z)]:
            if diff>0:differences.append(diff)
            else:raise ValueError('This view exceeds the 500-digit coordinate budget. Enlarge its spans or reduce its depth.')
        magnitudes.append(abs(z))
    if v['mapping']=='kepler':
        # Near a simple fold L(d+h)-L(d-h) is cubic in h. Ordinary
        # one-pixel derivative probes see its quadratic scale and miss the
        # finer separation between the two actual sampled sheets. Evaluate
        # the actual central sample block for every odd/even grid parity.
        # This includes both diagonal mirror pairs for even/even grids and
        # the horizontal/vertical mirror pairs beside an odd/odd center.
        def central_offsets(count,vertical=False):
            middle=count//2
            indices=range(max(0,middle-1),min(count,middle+2)) if count%2 else range(max(0,middle-2),min(count,middle+2))
            values=[(m.mpf(i)+m.mpf('.5'))/count-m.mpf('.5') for i in indices]
            return [-value for value in values] if vertical else values
        central=[]
        for y in central_offsets(height,True):
            for x in central_offsets(width):
                z,_=point(x,y);central.append(z);magnitudes.append(abs(z))
        for i,za in enumerate(central):
            for zb in central[i+1:]:
                difference=abs(za-zb)
                if difference: differences.append(difference)
                else:raise ValueError('The central Kepler samples exceed the coordinate precision budget.')
    if not differences:raise ValueError('Coordinates collapsed at the available precision; enlarge the viewport or choose more significant coordinate digits.')
    spacing=min(differences);magnitude=max(magnitudes)
    needed=max(16,int(m.ceil(m.log10(max(magnitude,1)/spacing)))+24)
    # Binary64 is offered only when its coordinate grid has a useful safety margin.
    use_double=float_safe and spacing>max(magnitude,1)*m.mpf('2e-13')
    if requested in ['auto',None]:digits=16 if use_double else max(40,needed)
    else:digits=int(requested)
    if digits<=16 and not float_safe:digits=max(40,needed)
    if digits<needed and not (digits==16 and use_double):
        digits=max(40,needed)
    if digits>500:raise ValueError(f'This view needs about {digits} decimal digits for distinct samples. This build supports 500; reduce depth or increase spans.')
    return dict(digits=digits,required_digits=needed,minimum_spacing=m.nstr(spacing,12),
        backend='compiled CPU / binary64' if digits<=16 else f'CPU / {digits}-digit arbitrary precision',
        coordinate_resolution='fresh computation at sample centers')

def grid_coordinates(viewport,width,height,digits,y0=0,rows=None):
    v=clean_viewport(viewport);rows=height-y0 if rows is None else rows
    xs=(np.arange(width)+.5)/width-.5
    ys=.5-(np.arange(y0,y0+rows)+.5)/height
    if digits<=16:
        c=special_constants(45);x=xs[None,:];y=ys[:,None]
        cr=float(v['center_re']);ci=float(v['center_im']);w=float(v['width']);h=float(v['height'])
        with np.errstate(all='ignore'):
            if v['mapping']=='cartesian':z=cr+w*x+1j*(ci+h*y)
            elif v['mapping']=='kepler':
                ur=float(c['d']) if v['u_re']=='dottie' else float(v['u_re'])
                u=ur+w*x+1j*(float(v['u_im'])+h*y);z=1j*u/np.cos(u)*np.exp(-u*np.tan(u))
            else:
                dep=float(v['depth'])+float(v['depth_span'])*y;power=float(v['lateral_power'])
                if v['mapping']=='log':delta=v['sign']*10.**dep;lateral=10.**(power*(dep-float(v['depth'])))
                else:delta=v['sign']*float(c['Cstar'])/10.**(2*dep);lateral=10.**(power*(float(v['depth'])-dep))
                z=cr+w*x*lateral+1j*(float(c['ystar'])+delta)
        z=np.broadcast_to(z,(rows,width)).copy()
        return np.ascontiguousarray(z.real),np.ascontiguousarray(z.imag)
    m,point,_,_=build_mapper(v,digits)
    re=[];im=[]
    for j in range(y0,y0+rows):
        rr=[];ii=[];yy=m.mpf(1)/2-(m.mpf(j)+m.mpf('.5'))/height
        for i in range(width):
            xx=(m.mpf(i)+m.mpf('.5'))/width-m.mpf(1)/2
            z,_=point(xx,yy);rr.append(m.nstr(z.real,digits+6));ii.append(m.nstr(z.imag,digits+6))
        re.append(rr);im.append(ii)
    return re,im

def coordinate(viewport,x_norm,y_norm,digits=80):
    m,point,_,_=build_mapper(viewport,digits);z,u=point(x_norm,y_norm)
    result=dict(re=m.nstr(z.real,digits),im=m.nstr(z.imag,digits))
    if u is not None:result['u']=dict(re=m.nstr(u.real,digits),im=m.nstr(u.imag,digits))
    return result

def navigate(payload):
    v=clean_viewport(payload.get('viewport'));digits=max(80,int(payload.get('digits',80)),working_digits(v))
    m,point,vals,_=build_mapper(v,digits);action=payload.get('action','pan');mode=v['mapping']
    dx=m.mpf(str(payload.get('dx',0)));dy=m.mpf(str(payload.get('dy',0)))
    if not m.isfinite(dx) or not m.isfinite(dy):raise ValueError('Navigation changes must be finite.')
    def put(k,value):v[k]=m.nstr(value,digits)
    remap_note=None
    if action=='crop':
        bounds=payload.get('bounds',{})
        try:x0,y0,x1,y1=(m.mpf(str(bounds[k])) for k in ['x0','y0','x1','y1'])
        except (KeyError,TypeError,ValueError):raise ValueError('A processing region needs x0, y0, x1 and y1 chart bounds.') from None
        if not all(m.isfinite(value) and abs(value)<=1000 for value in (x0,y0,x1,y1)):
            raise ValueError('Processing-region bounds must be finite chart coordinates within ±1000.')
        if x1<=x0 or y1<=y0:raise ValueError('Draw a processing region with positive width and height.')
        mx=(x0+x1)/2;my=(y0+y1)/2
        if mode in ['log','fold'] and vals['lateral_power']!=0:
            raise ValueError('Set the lateral-depth exponent to zero to process a rectangular region in this chart.')
        if mode=='kepler':
            put('u_re',vals['u_re']+vals['width']*mx);put('u_im',vals['u_im']+vals['height']*my)
        else:put('center_re',vals['center_re']+vals['width']*mx)
        put('width',vals['width']*(x1-x0))
        if mode in ['log','fold']:
            put('depth',vals['depth']+vals['depth_span']*my);put('depth_span',vals['depth_span']*(y1-y0))
        else:
            if mode=='cartesian':put('center_im',vals['center_im']+vals['height']*my)
            put('height',vals['height']*(y1-y0))
    elif action=='remap':
        target=payload.get('mapping','cartesian')
        if target not in ['cartesian','log','fold']:raise ValueError('Use the explicit u controls to select a Kepler chart.')
        center,_=point(0,0);step=m.mpf('1e-6')
        plus,_=point(0,step);minus,_=point(0,-step)
        local_height=abs((plus.imag-minus.imag)/(2*step))
        if local_height==0:local_height=vals['height']
        v['mapping']=target;put('center_re',center.real);put('center_im',center.imag)
        if target=='cartesian':put('height',local_height)
        else:
            delta=center.imag-m.mpf(special_constants(digits)['ystar'])
            if delta==0:raise ValueError('A finite logarithmic/fold chart needs a center on one side of the Dottie tip. Move its center slightly above or below the tip.')
            v['sign']=1 if delta>0 else -1
            if target=='log':
                put('depth',m.log10(abs(delta)));span=local_height/(m.ln(10)*abs(delta))
            else:
                C=m.mpf(special_constants(digits)['Cstar'])
                put('depth',m.log10(C/abs(delta))/2);span=local_height/(2*m.ln(10)*abs(delta))
            if not 0<span<=1000:raise ValueError('Matching this center would need a depth span beyond the evaluation budget. Move its center farther from the Dottie tip or reduce the vertical span.')
            put('depth_span',span)
        remap_note='Physical center and local vertical scale matched. Log and fold coordinates select one side of the Dottie tip and have nonlinear vertical spacing.'
    elif action=='recenter':
        v['mapping']='cartesian';v['center_re']=str(payload['re']);v['center_im']=str(payload['im'])
    elif action=='depth':
        if mode in ['log','fold']:put('depth',vals['depth']+dy)
        elif mode=='kepler':put('u_im',vals['u_im']+dy*vals['height'])
        else:put('center_im',vals['center_im']+dy*vals['height'])
    elif action=='pan':
        if mode=='kepler':put('u_re',vals['u_re']-dx*vals['width']);put('u_im',vals['u_im']-dy*vals['height'])
        else:
            put('center_re',vals['center_re']-dx*vals['width'])
            if mode=='cartesian':put('center_im',vals['center_im']-dy*vals['height'])
            else:put('depth',vals['depth']-dy*vals['depth_span'])
    elif action=='zoom':
        factor=m.mpf(str(payload.get('factor','.5')))
        if not 0<factor<=100:raise ValueError('Zoom factor must be in (0,100].')
        ax=m.mpf(str(payload.get('anchor_x',0)));ay=m.mpf(str(payload.get('anchor_y',0)))
        if not m.isfinite(ax) or not m.isfinite(ay):raise ValueError('Zoom anchors must be finite.')
        axis=payload.get('axis','both');old,_=point(ax,ay)
        if axis in ['both','lateral']:put('width',vals['width']*factor)
        if axis in ['both','depth']:
            if mode in ['log','fold']:
                put('depth_span',vals['depth_span']*factor)
                put('depth',vals['depth']+ay*vals['depth_span']*(1-factor))
            else:put('height',vals['height']*factor)
        if mode=='kepler':
            put('u_re',vals['u_re']+ax*(vals['width']-m.mpf(v['width'])))
            put('u_im',vals['u_im']+ay*(vals['height']-m.mpf(v['height'])))
        else:
            _,newpoint,_,_=build_mapper(v,digits);new,_=newpoint(ax,ay)
            put('center_re',m.mpf(v['center_re'])+old.real-new.real)
            if mode=='cartesian':put('center_im',m.mpf(v['center_im'])+old.imag-new.imag)
    else:raise ValueError('Unknown navigation operation.')
    build_mapper(v,digits)
    return dict(viewport=v,**({'remap_note':remap_note} if remap_note else {}))
