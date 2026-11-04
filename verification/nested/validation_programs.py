"""The explicit total programs used by the five validation presentations."""
def R(e,n,s):
    assert e in (0,1,2) and n>=0 and s>=0
    if e==0:return False
    if e==1:return n==0
    return n==0 and s==0

def k_constant(m):
    assert m>=1
    return 1

def k_linear(m):
    assert m>=1
    return m

def expected_uniform_outcome(e,period):
    # Only F_3=2 can possibly witness these particular predicates.
    if period!=2:return 'reject'
    if e==1:return 'accept'
    if e==2:return 'wait_one_step_then_reject'
    return 'reject'

def expected_guard(program,m,ell):
    return ell<(k_constant(m) if program=='constant' else k_linear(m))
