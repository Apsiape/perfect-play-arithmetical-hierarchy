from pathlib import Path
import os,sys

def peak():
    if os.name=='nt':
        import psutil
        return psutil.Process().memory_info().peak_wset
    import resource
    n=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return n if sys.platform=='darwin' else n*1024

def install_cap():
    if os.name!='nt':
        import resource
        resource.setrlimit(resource.RLIMIT_AS,(7*1024**3,7*1024**3))
        return
    import ctypes
    from ctypes import wintypes as wt
    class BASIC(ctypes.Structure):
        _fields_=[('process_time',ctypes.c_int64),('job_time',ctypes.c_int64),('flags',wt.DWORD),('minws',ctypes.c_size_t),('maxws',ctypes.c_size_t),('active',wt.DWORD),('affinity',ctypes.c_size_t),('priority',wt.DWORD),('scheduling',wt.DWORD)]
    class IO(ctypes.Structure):
        _fields_=[(n,ctypes.c_uint64) for n in ('ro','wo','oo','rt','wt','ot')]
    class EXT(ctypes.Structure):
        _fields_=[('basic',BASIC),('io',IO),('process_limit',ctypes.c_size_t),('job_limit',ctypes.c_size_t),('peak_process',ctypes.c_size_t),('peak_job',ctypes.c_size_t)]
    k=ctypes.WinDLL('kernel32',use_last_error=True);k.CreateJobObjectW.restype=wt.HANDLE
    k.SetInformationJobObject.argtypes=[wt.HANDLE,ctypes.c_int,ctypes.c_void_p,wt.DWORD]
    k.AssignProcessToJobObject.argtypes=[wt.HANDLE,wt.HANDLE];k.GetCurrentProcess.restype=wt.HANDLE
    job=k.CreateJobObjectW(None,None);lim=EXT();lim.basic.flags=0x100;lim.process_limit=7*1024**3
    assert k.SetInformationJobObject(job,9,ctypes.byref(lim),ctypes.sizeof(lim))
    assert k.AssignProcessToJobObject(job,k.GetCurrentProcess())
