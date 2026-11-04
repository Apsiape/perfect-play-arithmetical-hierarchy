from pathlib import Path
import numpy as np,json
OUT=Path(__file__).resolve().parent
rng=np.random.default_rng(20261103)
def U(n):
    q,r=np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))
    return q@np.diag(np.diag(r)/abs(np.diag(r)))
def st(a):return a.conj().T
def err(a,b):return float(np.linalg.norm(a-b,ord='fro'))
instances=['uniform-no','uniform-yes','uniform-lookup','comb-constant','comb-linear']
worst={};trials=200;instance_worst={name:0.0 for name in instances}
for trial in range(trials):
    powers=list(range(12))+[100,101,150,151]
    weights=np.repeat(np.exp2(-np.array(powers,dtype=float)),2);weights/=sum(weights)
    H=np.diag(weights);n=len(weights)
    uf,ue,ug,uh=[U(n) for _ in range(4)]
    R=np.zeros((n,n),complex)
    for j in range(0,n,2):R[j:j+2,j:j+2]=U(2)
    w0=ug@st(uf);w1=uh@st(ue);t=ug@R@st(ue)
    density=[uf@H@st(uf),2*ue@H@st(ue),2*ug@H@st(ug),4*uh@H@st(uh)]
    aa=[];ap=[];xx=[]
    for i in range(5):
        X=np.zeros((n,n),complex)
        for j,p in enumerate(powers):
            if p+1 in powers:
                k=powers.index(p+1);X[2*k:2*k+2,2*j:2*j+2]=(.2+.3*rng.random())*U(2)
        aa.append(ue@X@st(uf));ap.append(uh@X@st(ug));xx.append(st(w0)@t@aa[-1])
    L=np.zeros((n,n),complex);B=L.copy()
    for j in range(0,n,2):L[j:j+2,j:j+2]=U(2);B[j:j+2,j:j+2]=U(2)
    L0=uf@L@st(uf);L1=ug@L@st(ug);B0=uf@B@st(uf)
    ell=st(w0)@t@st(w1);checks={}
    checks['w0 calibration']=err(density[2]@w0,2*w0@density[0])
    checks['w1 calibration']=err(density[3]@w1,2*w1@density[1])
    checks['t centralizer']=err(density[2]@t,t@density[1])
    checks['t initial']=err(st(t)@t,np.eye(n));checks['t final']=err(t@st(t),np.eye(n))
    for i in range(5):
        checks[f'12_{i}']=err(ap[i],w1@aa[i]@st(w0))
        checks[f'14_{i}']=err(density[0]@xx[i],.5*xx[i]@density[0])
        for j in range(5):
            checks[f'15_inner_{i}{j}']=err(st(xx[i])@xx[j],st(aa[i])@aa[j])
            checks[f'15_range_{i}{j}']=err(w0@xx[i]@st(xx[j])@st(w0),t@aa[i]@st(aa[j])@st(t))
            checks[f'15_product_{i}{j}']=err(xx[i]@xx[j],ell@ap[i]@t@aa[j])
            checks[f'16_difference_{i}{j}']=err(xx[i]@xx[j]-xx[j]@xx[i],ell@(ap[i]@t@aa[j]-ap[j]@t@aa[i]))
            checks[f'17_difference_{i}{j}']=err(w0@(st(xx[i])@xx[j]-xx[j]@st(xx[i]))@st(w0),st(ap[i])@ap[j]-t@aa[j]@st(aa[i])@st(t))
        checks[f'18_difference_{i}']=err(w0@(L0@xx[i]-xx[i]@B0),L1@t@aa[i]-t@aa[i]@B0)
    for key,value in checks.items():worst[key]=max(worst.get(key,0),value)
    assert max(checks.values())<5e-12
    instance=instances[trial//40];instance_worst[instance]=max(instance_worst[instance],max(checks.values()))
result={'trials':trials,'batch_size':40,'arbitrary_batch_labels_maximum_residual':instance_worst,'instance_rows_loaded':False,'corner_spaces':'full 32-dimensional spaces','transports':'unitary','identity_12':'by construction','validation_kind':'instance-independent algebra check; not a soundness test','root_dimension':n,'identities_per_trial':len(checks),'assertions':trials*len(checks),'smallest_Schmidt_probability':float(min(weights)),'maximum_Frobenius_residual':max(worst.values()),'tolerance':5e-12,'inverse_density_used':False,'scope':'finite nilpotent modular contractions; no finite proper modular isometry','worst_by_identity':worst}
(OUT/'hostile-validation.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='worst_by_identity'},indent=2))
