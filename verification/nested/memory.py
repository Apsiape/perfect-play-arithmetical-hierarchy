"""Portable peak-memory telemetry; not part of the mathematical checks."""
import os
def peak_bytes():
    if os.name == 'nt':
        import psutil
        return psutil.Process().memory_info().peak_wset
    import resource,sys
    n=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return n if sys.platform == 'darwin' else n*1024
