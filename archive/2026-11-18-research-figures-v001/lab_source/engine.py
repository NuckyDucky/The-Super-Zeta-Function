"""Numerical reciprocal-tetration classifiers for local research exploration.

Positive codes are three-lap numerical closures, 0 is unresolved, -1 is an
arithmetic/resource horizon, and -4 is a phase-precision horizon. These are
finite numerical classifications. No horizon code is an escape certificate.
Binary64 previews use Numba/nogil when available. Arbitrary-precision calls
use a fresh cloned mpmath context, so concurrent requests have isolated precision.
"""
from __future__ import annotations

import cmath
import math
from concurrent.futures import CancelledError
from typing import Any
import numpy as np
import mpmath

try:
    from numba import njit
    NUMBA_AVAILABLE=True
except ImportError:
    NUMBA_AVAILABLE=False
    def njit(*args,**kwargs):
        def wrap(fn):return fn
        return wrap

MODES={'paired':0,'g_plus_1':1,'g_plus_0':2,'g_minus_0':3,'g_minus_1':4}
CLASSES={-4:'phase_precision_horizon',-1:'arithmetic_horizon',0:'unresolved'}
GUARDS={0:None,1:'positive_exponent_limit',2:'phase_precision_limit',3:'nonfinite_exponent'}

def _complex_value(value,default):
    if value is None:return complex(default)
    if isinstance(value,dict):return complex(float(value.get('re',value.get('real',0))),float(value.get('im',value.get('imaginary',0))))
    if isinstance(value,(list,tuple)):return complex(float(value[0]),float(value[1]))
    return complex(str(value).replace('i','j'))

def _configuration(settings:dict|None,digits:int):
    s=dict(settings or {})
    max_steps=int(s.get('max_steps',2048));max_period=int(s.get('max_period',128))
    if not 1<=max_steps<=200000:raise ValueError('max_steps must be between 1 and 200000')
    if not 1<=max_period<=4096:raise ValueError('max_period must be between 1 and 4096')
    mode=s.get('mode','paired')
    if mode not in MODES:raise ValueError('unknown orbit mode')
    tolerance_text=str(s.get('tolerance','1e-11'))
    validation_ctx=mpmath.mp.clone();validation_ctx.dps=max(30,int(digits)+5)
    validated_tol=validation_ctx.mpf(tolerance_text)
    if not validation_ctx.isfinite(validated_tol) or not 0<validated_tol<1:
        raise ValueError('tolerance must be positive and below one')
    tol=float(validated_tol)
    if digits<=16 and tol==0:
        raise ValueError('this tolerance requires arbitrary precision; increase digits')
    for option in ('phase_limit','positive_exponent_limit'):
        if s.get(option) is not None:
            value=validation_ctx.mpf(str(s[option]))
            if not validation_ctx.isfinite(value) or not value>0:
                raise ValueError(option+' must be finite and positive')
    checkpoints=sorted(set(int(x) for x in s.get('checkpoints',[512,1024,2048,4096,8000,16384,32768,65536,131072]) if 0<int(x)<=max_steps)|{max_steps})
    legacy=bool(s.get('legacy_zero_cutoff',False))
    return {'max_steps':max_steps,'max_period':max_period,'mode':mode,'mode_id':MODES[mode],
        'tolerance':tol,'tolerance_text':tolerance_text,'checkpoints':checkpoints,
        'legacy':legacy,'initial_P':s.get('initial_P',s.get('P0','1')),
        'initial_Q':s.get('initial_Q',s.get('Q0','1')),
        'phase_limit':s.get('phase_limit',None),'positive_exponent_limit':s.get('positive_exponent_limit',None)}

@njit(cache=True,nogil=True)
def _component(z):return max(abs(z.real),abs(z.imag))

@njit(cache=True,nogil=True)
def _exp64(z,phase_limit,zero_cutoff):
    if not math.isfinite(z.real) or not math.isfinite(z.imag):return 0j,3,0
    if z.real<zero_cutoff:return 0j,0,1
    if z.real>700.:return 0j,1,0
    if abs(z.imag)>phase_limit:return 0j,2,0
    return cmath.exp(z),0,0

@njit(cache=True,nogil=True)
def _logabs(z):
    a=abs(z)
    return math.log(a) if a>0 else -math.inf

@njit(cache=True,nogil=True)
def _period64(hp,hq,n,mode_id,max_period,tol):
    length=len(hp)
    for period in range(1,min(max_period,n//3)+1):
        worst=0.;scale=1.
        # Endpoint prefilter, followed by all phase offsets on three laps.
        for channel in range(2 if mode_id==0 else 1):
            h=hp if channel==0 else hq
            a,b,c=h[n%length],h[(n-period)%length],h[(n-2*period)%length]
            worst=max(worst,_component(a-b),_component(b-c))
            scale=max(scale,_component(a),_component(b),_component(c))
        if worst>tol*scale:continue
        for offset in range(period):
            for channel in range(2 if mode_id==0 else 1):
                h=hp if channel==0 else hq
                a,b,c=h[(n-offset)%length],h[(n-period-offset)%length],h[(n-2*period-offset)%length]
                worst=max(worst,_component(a-b),_component(b-c))
                scale=max(scale,_component(a),_component(b),_component(c))
        if worst<=tol*scale:return period,worst/scale
    return 0,math.nan

@njit(cache=True,nogil=True)
def _multiplier64(L,hp,hq,n,period,mode_id):
    length=len(hp)
    if L==0j:return -math.inf
    ll=_logabs(L)
    if mode_id==0:
        r0=0.;r1=0.
        for k in range(n-period+1,n+1):
            loga=ll+_logabs(hp[k%length]);logb=ll+_logabs(hq[k%length])
            old=r0;r0=loga+r1;r1=logb+old
        return max(r0,r1) if period%2==0 else (r0+r1)/2
    X=-L if mode_id>=3 else L
    total=0.
    for k in range(n-period+1,n+1):
        previous=hp[(k-1)%length];middle=cmath.exp(-X*previous)
        total+=2*ll+(-X*previous).real+(X*middle).real
    return total

@njit(cache=True,nogil=True)
def _point64(L,mode_id,max_steps,max_period,tol,checkpoints,phase_limit,zero_cutoff,P,Q):
    history=3*max_period+1
    hp=np.zeros(history,np.complex128);hq=np.zeros(history,np.complex128)
    if mode_id>0:P=0j if mode_id in (2,3) else 1+0j
    hp[0]=P;hq[0]=Q;ci=0;flushes=0
    for n in range(1,max_steps+1):
        if mode_id==0:
            pn,guard,fl=_exp64(L*Q,phase_limit,zero_cutoff);flushes+=fl
            if guard:return (-4 if guard==2 else -1),n,math.nan,math.nan,guard,flushes,P,Q
            qn,guard,fl=_exp64(-L*P,phase_limit,zero_cutoff);flushes+=fl
            if guard:return (-4 if guard==2 else -1),n,math.nan,math.nan,guard,flushes,P,Q
            P,Q=pn,qn
        else:
            X=-L if mode_id>=3 else L
            middle,guard,fl=_exp64(-X*P,phase_limit,zero_cutoff);flushes+=fl
            if guard:return (-4 if guard==2 else -1),n,math.nan,math.nan,guard,flushes,P,Q
            P,guard,fl=_exp64(X*middle,phase_limit,zero_cutoff);flushes+=fl
            if guard:return (-4 if guard==2 else -1),n,math.nan,math.nan,guard,flushes,P,Q
        hp[n%history]=P;hq[n%history]=Q
        if ci<len(checkpoints) and n==checkpoints[ci]:
            ci+=1
            period,closure=_period64(hp,hq,n,mode_id,max_period,tol)
            if period:
                lm=_multiplier64(L,hp,hq,n,period,mode_id)
                return period,n,closure,lm,0,flushes,P,Q
    return 0,max_steps,math.nan,math.nan,0,flushes,P,Q

@njit(cache=True,nogil=True)
def _grid64(reals,imags,mode_id,max_steps,max_period,tol,checkpoints,phase_limit,zero_cutoff,P,Q):
    count=len(reals)
    codes=np.zeros(count,np.int32);steps=np.zeros(count,np.int32)
    closure=np.full(count,np.nan);multiplier=np.full(count,np.nan)
    guards=np.zeros(count,np.int8);flushes=np.zeros(count,np.int32)
    for i in range(count):
        row=_point64(complex(reals[i],imags[i]),mode_id,max_steps,max_period,tol,checkpoints,phase_limit,zero_cutoff,P,Q)
        codes[i],steps[i],closure[i],multiplier[i],guards[i],flushes[i]=row[:6]
    return codes,steps,closure,multiplier,guards,flushes

def _mp_complex(ctx,value,default=1):
    if value is None:return ctx.mpc(default)
    if isinstance(value,dict):return ctx.mpc(str(value.get('re',value.get('real',0))),str(value.get('im',value.get('imaginary',0))))
    if isinstance(value,(list,tuple)):return ctx.mpc(str(value[0]),str(value[1]))
    text=str(value).strip().replace(' ','').replace('i','j').strip('()')
    if not text.endswith('j'):return ctx.mpc(ctx.mpf(text))
    body=text[:-1];split=-1
    for i in range(1,len(body)):
        if body[i] in '+-' and body[i-1] not in 'eE':split=i
    real,imag=(body[:split],body[split:]) if split>=0 else ('0',body)
    if imag in ('','+','-'):imag+='1'
    return ctx.mpc(ctx.mpf(real),ctx.mpf(imag))

def _point_mp(re,im,cfg,digits,cancel_event=None):
    ctx=mpmath.mp.clone();ctx.dps=int(digits)
    L=ctx.mpc(str(re),str(im));mode=cfg['mode_id'];tol=ctx.mpf(cfg['tolerance_text'])
    phase=ctx.power(10,max(1,digits-10))
    if cfg['phase_limit'] is not None:phase=min(phase,ctx.mpf(str(cfg['phase_limit'])))
    real_limit=ctx.mpf(str(cfg['positive_exponent_limit'] or 1000000))
    zero_cutoff=ctx.log(tol)-20 if cfg['legacy'] else None
    hp=[_mp_complex(ctx,cfg['initial_P']) if mode==0 else ctx.mpc(0 if mode in (2,3) else 1)]
    hq=[_mp_complex(ctx,cfg['initial_Q'])]
    P,Q=hp[0],hq[0];flushed=0;ci=0;history=3*cfg['max_period']+1
    def component(z):return max(abs(z.real),abs(z.imag))
    def exp_checked(z):
        nonlocal flushed
        if not ctx.isfinite(z):return None,3
        if zero_cutoff is not None and z.real<zero_cutoff:flushed+=1;return ctx.mpc(0),0
        if z.real>real_limit:return None,1
        if abs(z.imag)>phase:return None,2
        return ctx.exp(z),0
    code=0;closure=None;lm=None;guard=0
    for n in range(1,cfg['max_steps']+1):
        if cancel_event is not None and n%32==1 and cancel_event.is_set():
            raise CancelledError('numerical computation cancelled')
        if mode==0:
            pn,guard=exp_checked(L*Q)
            if guard:break
            qn,guard=exp_checked(-L*P)
            if guard:break
            P,Q=pn,qn
        else:
            X=-L if mode>=3 else L
            middle,guard=exp_checked(-X*P)
            if guard:break
            pn,guard=exp_checked(X*middle)
            if guard:break
            P=pn
        hp.append(P);hq.append(Q)
        if len(hp)>history:hp.pop(0);hq.pop(0)
        if ci>=len(cfg['checkpoints']) or n!=cfg['checkpoints'][ci]:continue
        ci+=1
        for p in range(1,min(cfg['max_period'],n//3)+1):
            worst=ctx.mpf(0);scale=ctx.mpf(1)
            channels=(hp,hq) if mode==0 else (hp,)
            for h in channels:
                a,b,c=h[-1],h[-1-p],h[-1-2*p]
                worst=max(worst,component(a-b),component(b-c));scale=max(scale,component(a),component(b),component(c))
            if worst>tol*scale:continue
            for offset in range(p):
                for h in channels:
                    a,b,c=h[-1-offset],h[-1-p-offset],h[-1-2*p-offset]
                    worst=max(worst,component(a-b),component(b-c));scale=max(scale,component(a),component(b),component(c))
            if worst<=tol*scale:code=p;closure=worst/scale;break
        if code:
            if not L:lm=ctx.ninf
            elif mode==0:
                ll=ctx.log(abs(L));r0=r1=ctx.mpf(0)
                for k in range(-code,0):
                    loga=ll+ctx.log(abs(hp[k]));logb=ll+ctx.log(abs(hq[k]))
                    r0,r1=loga+r1,logb+r0
                lm=max(r0,r1) if code%2==0 else (r0+r1)/2
            else:
                X=-L if mode>=3 else L;lm=ctx.mpf(0)
                for k in range(-code,0):
                    previous=hp[k-1];middle=ctx.exp(-X*previous)
                    lm+=2*ctx.log(abs(L))+(-X*previous).real+(X*middle).real
            break
    else:n=cfg['max_steps']
    if guard:code=-4 if guard==2 else -1
    return {'code':code,'steps':n,'closure':closure,'log_multiplier':lm,'guard':guard,
        'flushes':flushed,'P':P,'Q':Q,'context':ctx,'phase_limit':phase,'positive_exponent_limit':real_limit}

def _clock(mode):return 'simultaneous ordered-pair updates F_L' if mode=='paired' else 'scalar returns g_'+('-L' if mode.startswith('g_minus') else 'L')

def classify_grid(reals,imags,settings=None,digits=16,*,cancel_event=None):
    """Classify same-shaped coordinates; exact decimal strings select high precision.

    All positive codes are numerical candidate periods in the returned clock.
    Binary64 default phase budget is1e6; legacy mode preserves source1e14 and
    tolerance-derived zero clipping. High precision defaults to phase10^(dps-10)
    and real-exponent resource cap1e6, with no tolerance-based zero clipping.
    """
    digits=int(digits)
    if not 16<=digits<=2000:raise ValueError('digits must be between16 and2000')
    cfg=_configuration(settings,digits)
    if cancel_event is not None and cancel_event.is_set():raise CancelledError('numerical computation cancelled')
    reals=np.asarray(reals);imags=np.asarray(imags)
    if reals.shape!=imags.shape:raise ValueError('real and imaginary grids must have the same shape')
    shape=reals.shape
    if digits<=16:
        phase=float(cfg['phase_limit'] or (1e14 if cfg['legacy'] else 1e6))
        if not cfg['legacy']:phase=min(phase,1e6)
        cutoff=math.log(cfg['tolerance'])-20 if cfg['legacy'] else -745.
        rf=np.asarray(reals,dtype=np.float64).ravel();inf=np.asarray(imags,dtype=np.float64).ravel()
        def run64(a,b):
            return _grid64(a,b,cfg['mode_id'],cfg['max_steps'],cfg['max_period'],cfg['tolerance'],
                np.asarray(cfg['checkpoints'],dtype=np.int64),phase,cutoff,
                _complex_value(cfg['initial_P'],1),_complex_value(cfg['initial_Q'],1))
        if cancel_event is None:rows=run64(rf,inf)
        else:
            batches=[]
            for start in range(0,len(rf),16):
                if cancel_event.is_set():raise CancelledError('numerical computation cancelled')
                batches.append(run64(rf[start:start+16],inf[start:start+16]))
            rows=tuple(np.concatenate([batch[k] for batch in batches]) for k in range(6))
        result={k:v.reshape(shape) for k,v in zip(('code','steps','closure','log_multiplier','guard','zero_flushes'),rows)}
        result['backend']='numba-binary64' if NUMBA_AVAILABLE else 'python-binary64'
    else:
        result={k:np.zeros(shape,dtype=np.int32 if k in ('code','steps','guard','zero_flushes') else float)
            for k in ('code','steps','closure','log_multiplier','guard','zero_flushes')}
        for index in np.ndindex(shape):
            if cancel_event is not None and cancel_event.is_set():raise CancelledError('numerical computation cancelled')
            row=_point_mp(str(reals[index]),str(imags[index]),cfg,digits,cancel_event)
            for key in ('code','steps','guard'):result[key][index]=row[key]
            result['zero_flushes'][index]=row['flushes']
            for key in ('closure','log_multiplier'):result[key][index]=float(row[key]) if row[key] is not None else math.nan
        result['backend']='mpmath-'+str(digits)+'dps'
    result.update({'digits':digits,'clock':_clock(cfg['mode']),'classification_scope':'finite numerical three-lap closure',
        'legacy_zero_cutoff':cfg['legacy'],'mode':cfg['mode']})
    return result

def _json_float(value):
    if value is None:return None
    f=float(value)
    return f if math.isfinite(f) else ('-Infinity' if f<0 else 'Infinity')

def classify_point(re,im,settings=None,digits=80,*,cancel_event=None):
    """High-precision inspector with exact coordinate strings and numerical scope."""
    digits=int(digits)
    if not 16<=digits<=2000:raise ValueError('digits must be between16 and2000')
    cfg=_configuration(settings,digits)
    row=_point_mp(str(re),str(im),cfg,digits,cancel_event);ctx=row['context'];code=row['code'];lm=row['log_multiplier']
    classification=CLASSES.get(code,'candidate_fixed_pair' if code==1 and cfg['mode']=='paired' else 'candidate_fixed_point' if code==1 else 'candidate_periodic_orbit')
    stability='unresolved'
    if code>0 and lm is not None:
        stability='near_neutral' if abs(lm)<ctx.mpf('1e-4') else 'numerically_attracting' if lm<0 else 'numerically_repelling'
    def enc(z):
        if z is None:return None
        return {'re':ctx.nstr(z.real,digits),'im':ctx.nstr(z.imag,digits)}
    flags=[]
    if row['flushes']:flags.append('legacy_zero_clipping')
    if stability=='near_neutral':flags.append('near_parabolic_or_neutral')
    return {'code':code,'class':classification,'classification':classification,
        'detected_period':code if code>0 else None,'period':code if code>0 else None,'steps':row['steps'],
        'closure':_json_float(row['closure']),'closure_decimal':ctx.nstr(row['closure'],digits) if row['closure'] is not None else None,
        'log_multiplier':_json_float(lm),'log_multiplier_decimal':ctx.nstr(lm,digits) if lm is not None else None,
        'spectral_radius':ctx.nstr(ctx.exp(lm),min(digits,80)) if lm is not None else None,
        'stability_numeric':stability,'guard_reason':GUARDS[row['guard']],
        'precision_digits':digits,'digits':digits,'backend':'mpmath-'+str(digits)+'dps',
        'clock':_clock(cfg['mode']),'mode':cfg['mode'],'parameter':{'re':str(re),'im':str(im)},
        'final':{'P':enc(row['P']),'Q':enc(row['Q'])} if cfg['mode']=='paired' else {'z':enc(row['P'])},
        'phase_limit':ctx.nstr(row['phase_limit'],20),'positive_exponent_limit':str(row['positive_exponent_limit']),
        'zero_flushes':row['flushes'],'flags':flags,'settings':{k:cfg[k] for k in ('max_steps','max_period','tolerance_text','checkpoints')},
        'evidence':'numerical three-complete-lap closure and analytic Jacobian product evaluated at computed states'}

def colorize(result,mode='period'):
    """RGB array with separate unresolved/arithmetic/precision classes."""
    import colorsys
    codes=np.asarray(result['code']);out=np.empty(codes.shape+(3,),dtype=np.uint8)
    out[:]=[121,135,153];out[codes==-1]=[32,39,54];out[codes==-4]=[135,76,157]
    out[codes==-2]=[240,181,73];out[codes==1]=[63,116,178]
    for p in np.unique(codes[codes>=2]):
        rgb=colorsys.hsv_to_rgb((float(p)*.61803398875)%1,.72,.95-.25*min(math.log(float(p))/math.log(128),1))
        out[codes==p]=[round(255*x) for x in rgb]
    if mode=='classification':
        out[codes>=2]=[43,186,170]
    elif mode in ('multiplier','stability'):
        values=np.asarray(result['log_multiplier']);mask=(codes>0)&np.isfinite(values)
        t=.5+.5*np.tanh(values[mask]/2)
        out[mask]=np.column_stack((55+180*t,160-100*t,175-110*t)).astype(np.uint8)
    elif mode in ('steps','convergence'):
        values=np.asarray(result['steps']);mask=codes>0
        maximum=max(1,float(values.max()));t=np.log1p(values[mask])/math.log1p(maximum)
        out[mask]=np.column_stack((35+175*t,180-70*t,210-35*t)).astype(np.uint8)
    return out
