"""Actual CUDA FP64 numerical parameter rasterization with the CPU engine contract.

One CUDA thread advances one marked orbit. Histories and all period tests live
on the GPU. Host code only transfers coordinate batches and final observables.
Kernel launches advance at most256 updates by default, allowing cancellation
between short launches. The same numerical scope and horizon codes as engine.py
apply; this module does not classify a numerical horizon as mathematical escape.
"""
from __future__ import annotations
from concurrent.futures import CancelledError
import math
import os
from pathlib import Path
import threading
import time
import numpy as np
import engine

_LOCK=threading.RLock()
_CP=None
_KERNEL=None
_ERROR=None

CUDA_SOURCE=r'''
struct C { double r; double i; };
__device__ __forceinline__ C z(double r,double i){ C a={r,i}; return a; }
__device__ __forceinline__ C mul(C a,C b){return z(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r);}
__device__ __forceinline__ C neg(C a){return z(-a.r,-a.i);}
__device__ __forceinline__ C sub(C a,C b){return z(a.r-b.r,a.i-b.i);}
__device__ __forceinline__ double comp(C a){return fmax(fabs(a.r),fabs(a.i));}
__device__ __forceinline__ double logabs(C a){return log(hypot(a.r,a.i));}
__device__ __forceinline__ C rawexp(C a){
    double s,c; sincos(a.i,&s,&c); double e=exp(a.r);return z(e*c,e*s);
}
__device__ __forceinline__ int checkedexp(C a,C *out,double phase,double cutoff,int *flush){
    if(!isfinite(a.r)||!isfinite(a.i))return 3;
    if(a.r<cutoff){*out=z(0.,0.);(*flush)++;return 0;}
    if(a.r>700.)return 1;
    if(fabs(a.i)>phase)return 2;
    *out=rawexp(a);return 0;
}
__device__ __forceinline__ C get(C *h,int n,int len,int count,int tid){return h[(n%len)*count+tid];}
extern "C" __global__ void classify(
    const double *re,const double *im,int count,int mode,int maxsteps,int maxperiod,
    double tol,const int *checkpoints,int ncp,double phase,double cutoff,
    double pr,double pi,double qr,double qi,int startn,int stopn,
    C *hp,C *hq,int *codes,int *steps,double *closures,double *logmult,
    signed char *guards,int *flushes){
    int tid=blockIdx.x*blockDim.x+threadIdx.x;
    if(tid>=count||codes[tid]!=-5)return;
    int len=3*maxperiod+1,flush=flushes[tid],ci=0;
    C L=z(re[tid],im[tid]),P,Q;
    C X=(mode>=3)?neg(L):L;
    if(startn==1){
        P=z(pr,pi);Q=z(qr,qi);
        if(mode>0)P=z((mode==2||mode==3)?0.:1.,0.);
        hp[tid]=P;hq[tid]=Q;
    }else{P=get(hp,startn-1,len,count,tid);Q=get(hq,startn-1,len,count,tid);}
    while(ci<ncp&&checkpoints[ci]<startn)ci++;
    for(int n=startn;n<=stopn;n++){
        C pn,qn;int guard=0;
        if(mode==0){
            guard=checkedexp(mul(L,Q),&pn,phase,cutoff,&flush);
            if(!guard)guard=checkedexp(neg(mul(L,P)),&qn,phase,cutoff,&flush);
        }else{
            C middle;guard=checkedexp(neg(mul(X,P)),&middle,phase,cutoff,&flush);
            if(!guard)guard=checkedexp(mul(X,middle),&pn,phase,cutoff,&flush);
            qn=Q;
        }
        if(guard){codes[tid]=(guard==2)?-4:-1;steps[tid]=n;guards[tid]=guard;flushes[tid]=flush;return;}
        P=pn;Q=qn;hp[(n%len)*count+tid]=P;hq[(n%len)*count+tid]=Q;
        if(ci>=ncp||n!=checkpoints[ci])continue;
        ci++;
        int upper=(maxperiod<n/3)?maxperiod:n/3,channels=(mode==0)?2:1;
        for(int period=1;period<=upper;period++){
            double worst=0.,scale=1.;
            for(int channel=0;channel<channels;channel++){
                C *h=(channel==0)?hp:hq;
                C a=get(h,n,len,count,tid),b=get(h,n-period,len,count,tid),c=get(h,n-2*period,len,count,tid);
                worst=fmax(worst,fmax(comp(sub(a,b)),comp(sub(b,c))));
                scale=fmax(scale,fmax(comp(a),fmax(comp(b),comp(c))));
            }
            if(worst>tol*scale)continue;
            for(int offset=0;offset<period;offset++){
                for(int channel=0;channel<channels;channel++){
                    C *h=(channel==0)?hp:hq;
                    C a=get(h,n-offset,len,count,tid),b=get(h,n-period-offset,len,count,tid),c=get(h,n-2*period-offset,len,count,tid);
                    worst=fmax(worst,fmax(comp(sub(a,b)),comp(sub(b,c))));
                    scale=fmax(scale,fmax(comp(a),fmax(comp(b),comp(c))));
                }
            }
            if(worst>tol*scale)continue;
            double lm=-1.0/0.0;
            if(L.r!=0.||L.i!=0.){
                double ll=logabs(L);
                if(mode==0){
                    double r0=0.,r1=0.;
                    for(int k=n-period+1;k<=n;k++){
                        double a=ll+logabs(get(hp,k,len,count,tid));
                        double b=ll+logabs(get(hq,k,len,count,tid));
                        double previous=r0;r0=a+r1;r1=b+previous;
                    }
                    lm=(period%2==0)?fmax(r0,r1):(r0+r1)/2.;
                }else{
                    lm=0.;
                    for(int k=n-period+1;k<=n;k++){
                        C previous=get(hp,k-1,len,count,tid);
                        C e=neg(mul(X,previous));C middle=rawexp(e);
                        lm+=2.*ll+e.r+mul(X,middle).r;
                    }
                }
            }
            codes[tid]=period;steps[tid]=n;closures[tid]=worst/scale;logmult[tid]=lm;flushes[tid]=flush;return;
        }
    }
    steps[tid]=stopn;flushes[tid]=flush;
    if(stopn==maxsteps)codes[tid]=0;
}
'''

def _load():
    global _CP,_KERNEL,_ERROR
    with _LOCK:
        if _KERNEL is not None:return _CP,_KERNEL
        try:
            cache=Path(os.environ.setdefault('CUPY_CACHE_DIR',str(Path(__file__).resolve().parent/'data'/'cuda-cache')))
            cache.mkdir(parents=True,exist_ok=True)
            import cupy as cp
            if cp.cuda.runtime.getDeviceCount()<1:raise RuntimeError('No CUDA device is visible.')
            kernel=cp.RawKernel(CUDA_SOURCE,'classify',options=('--std=c++11','--fmad=false'))
            kernel.compile()
            _CP=cp;_KERNEL=kernel;_ERROR=None
            return cp,kernel
        except Exception as error:
            _ERROR=f'{type(error).__name__}: {error}'
            raise RuntimeError('CUDA numerical rasterizer is unavailable: '+_ERROR) from error

def available():
    try:_load();return True
    except Exception:return False

def device_info():
    if not available():return {'available':False,'error':_ERROR,'scope':'optional CUDA FP64 numerical rasterization'}
    cp=_CP;p=cp.cuda.runtime.getDeviceProperties(cp.cuda.runtime.getDevice())
    name=p['name'].decode() if isinstance(p['name'],bytes) else str(p['name'])
    free,total=cp.cuda.runtime.memGetInfo()
    return {'available':True,'name':name,'cupy_version':cp.__version__,
        'cuda_runtime_version':int(cp.cuda.runtime.runtimeGetVersion()),
        'cuda_driver_version':int(cp.cuda.runtime.driverGetVersion()),
        'compute_capability':f"{p['major']}.{p['minor']}",
        'total_memory_bytes':int(total),'free_memory_bytes':int(free),
        'arithmetic':'CUDA native FP64 complex orbit arithmetic',
        'numerical_work':'per-pixel iteration, guards, three-lap period detection and analytic cycle Jacobian product on GPU',
        'source':'CuPy RawKernel / NVRTC','fused_multiply_add':False}

def classify_grid(reals,imags,settings=None,digits=16,*,cancel_event=None):
    """Same mathematical array contract as engine.classify_grid; FP64 only.

    Memory usage is batched by history length. High-precision coordinates must
    use the CPU arbitrary-precision engine rather than being rounded into CUDA.
    """
    if int(digits)!=16:raise ValueError('CUDA rasterization uses FP64; arbitrary-precision requests use CPU.')
    cfg=engine._configuration(settings,16);settings=dict(settings or {})
    rf=np.asarray(reals,dtype=np.float64);inf=np.asarray(imags,dtype=np.float64)
    if rf.shape!=inf.shape:raise ValueError('real and imaginary grids must have the same shape')
    shape=rf.shape;rf=np.ascontiguousarray(rf.ravel());inf=np.ascontiguousarray(inf.ravel())
    phase=float(cfg['phase_limit'] or (1e14 if cfg['legacy'] else 1e6))
    if not cfg['legacy']:phase=min(phase,1e6)
    cutoff=math.log(cfg['tolerance'])-20 if cfg['legacy'] else -745.
    P=engine._complex_value(cfg['initial_P'],1);Q=engine._complex_value(cfg['initial_Q'],1)
    chunk=int(settings.get('gpu_step_chunk',256))
    if not 32<=chunk<=2048:raise ValueError('gpu_step_chunk must be between32 and2048')
    budget_mb=int(settings.get('gpu_memory_mb',384))
    if not 32<=budget_mb<=1024:raise ValueError('gpu_memory_mb must be between32 and1024')
    if cancel_event is not None and cancel_event.is_set():raise CancelledError('CUDA render cancelled')
    host={k:np.zeros(len(rf),dtype=dtype) for k,dtype in
        [('code',np.int32),('steps',np.int32),('closure',float),('log_multiplier',float),('guard',np.int8),('zero_flushes',np.int32)]}
    started=time.perf_counter();launches=0;batches=0;peak_working=0;max_batch=0;max_roundtrip=0.
    with _LOCK:
        cp,kernel=_load();free,total=cp.cuda.runtime.memGetInfo()
        budget=min(budget_mb*1024**2,int(free*.35))
        history=3*cfg['max_period']+1
        per_pixel=32*history+96
        batch_cap=max(1,min(65536,budget//per_pixel))
        cp_checkpoints=cp.asarray(cfg['checkpoints'],dtype=cp.int32)
        for first in range(0,len(rf),batch_cap):
            if cancel_event is not None and cancel_event.is_set():raise CancelledError('CUDA render cancelled')
            last=min(len(rf),first+batch_cap);count=last-first;batches+=1
            cr=cp.asarray(rf[first:last]);ci=cp.asarray(inf[first:last])
            hp=cp.empty((history,count),dtype=cp.complex128);hq=cp.empty_like(hp)
            codes=cp.full(count,-5,dtype=cp.int32);steps=cp.zeros(count,dtype=cp.int32)
            closure=cp.full(count,cp.nan,dtype=cp.float64);lm=cp.full(count,cp.nan,dtype=cp.float64)
            guard=cp.zeros(count,dtype=cp.int8);flush=cp.zeros(count,dtype=cp.int32)
            max_batch=max(max_batch,count)
            peak_working=max(peak_working,sum(array.nbytes for array in
                (cp_checkpoints,cr,ci,hp,hq,codes,steps,closure,lm,guard,flush)))
            for start in range(1,cfg['max_steps']+1,chunk):
                if cancel_event is not None and cancel_event.is_set():raise CancelledError('CUDA render cancelled')
                stop=min(cfg['max_steps'],start+chunk-1)
                roundtrip_started=time.perf_counter()
                kernel(((count+127)//128,),(128,),
                    (cr,ci,np.int32(count),np.int32(cfg['mode_id']),np.int32(cfg['max_steps']),np.int32(cfg['max_period']),
                     np.float64(cfg['tolerance']),cp_checkpoints,np.int32(len(cfg['checkpoints'])),np.float64(phase),np.float64(cutoff),
                     np.float64(P.real),np.float64(P.imag),np.float64(Q.real),np.float64(Q.imag),np.int32(start),np.int32(stop),
                     hp,hq,codes,steps,closure,lm,guard,flush))
                # The scalar read synchronizes this stream, including the
                # classifier. A separate pre-reduction stream synchronization
                # added a redundant host/device barrier on every step chunk.
                unfinished=bool(cp.any(codes==-5).item());launches+=1
                max_roundtrip=max(max_roundtrip,time.perf_counter()-roundtrip_started)
                if not unfinished:break
            for key,value in zip(host,(codes,steps,closure,lm,guard,flush)):
                host[key][first:last]=cp.asnumpy(value)
            del hp,hq,cr,ci,codes,steps,closure,lm,guard,flush
    result={k:v.reshape(shape) for k,v in host.items()}
    result.update(digits=16,backend='cuda-fp64',clock=engine._clock(cfg['mode']),mode=cfg['mode'],
        classification_scope='finite numerical three-complete-lap closure computed on CUDA',
        legacy_zero_cutoff=cfg['legacy'],gpu=dict(device=device_info()['name'],batches=batches,
        kernel_launches=launches,history_memory_budget_mb=budget_mb,step_chunk=chunk,
        actual_memory_budget_bytes=int(budget),batch_capacity_pixels=int(batch_cap),
        largest_batch_pixels=max_batch,peak_working_array_bytes=int(peak_working),
        max_chunk_roundtrip_seconds=max_roundtrip,
        scheduling='history-memory-bounded batches; one host synchronization per step chunk',
        elapsed_seconds=time.perf_counter()-started))
    return result
