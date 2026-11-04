"""Exact small-truncation audit, size normalization, and streamable layout budget."""
from pathlib import Path
from fractions import Fraction as F
import json,time,ctypes
from ctypes import wintypes as wt
O=Path(__file__).resolve().parent;start=time.perf_counter()
results={}
for directory in ('expanded','factored'):
    p=json.loads((O/directory/'counts_primary.json').read_text());Q=p['questions_per_party'];n=p['scalar_qubits'];V=p['projection_variables'];h={int(d):c for d,c in p['row_dimensions'].items()}
    defects=[x for x in p['app_details'] if x['name'].startswith('fock_') and x['name'][5:7]==x['name'][8:10]]
    assert len(defects)==4 and all(x['L']==2 and x['d']==16 for x in defects)
    levels=[]
    for m in range(5):
        basis=[(d,x,y) for d in range(m+1) for x in range(2**d) for y in range(2**d)]
        weights={v:F(1,16**v[0]) for v in basis};normal=sum(weights.values(),F(0));weights={v:w/normal for v,w in weights.items()}
        mass=sum((w for v,w in weights.items() if v[0]==m),F(0));assert mass==F(3,4**(m+1)-1)
        ranges=[]
        for a,b in ((0,0),(0,1),(1,0),(1,1)):
            creation={v:(v[0]+1,2*v[1]+a,2*v[2]+b) for v in basis if v[0]<m}
            assert len(set(creation.values()))==len(creation)
            for v,w in creation.items():assert weights[w]==weights[v]/16
            ranges.append(set(creation.values()))
            # Coordinate and boundary endpoint equations, directly on basis vectors.
            for v,w in creation.items():
                d,x,y=v;dd,xx,yy=w;N=2**d;NN=2**dd
                assert ((xx+1)%NN,yy)==((2*x+1,2*y+b) if a==0 else (2*((x+1)%N),2*y+b))
                assert (xx,(yy+1)%NN)==((2*x+a,2*y+1) if b==0 else (2*x+a,2*((y+1)%N)))
                assert (xx==0)==(a==0 and x==0);assert (yy==0)==(b==0 and y==0)
                assert F(1,2**yy)==F(1,2**b)*F(1,2**y)**2
        assert set.union(*ranges)==set(basis)-{(0,0,0)}
        for i in range(4):
            for j in range(i):assert not ranges[i]&ranges[j]
        row_losses=[F(4*r['L']**2,r['d']**3)*F(2,363)*mass for r in defects]
        loss=sum(row_losses,F(0))/Q**2
        assert loss==mass/F(11616*Q**2)
        levels.append({'m':m,'tree_dimension':len(basis),'top_mass':str(mass),'failed_rows':[r['name'] for r in defects],'exact_game_loss':str(loss)})
    assert all(F(a['exact_game_loss'])>F(b['exact_game_loss']) for a,b in zip(levels,levels[1:]))
    binding=18*(n//2)+2*p['question_kinds']['cross_axes']+4*n*V+2*n+sum((d-1)*(d.bit_length()-1) for d in h)+4*sum((d-1)*c for d,c in h.items())
    joints=sum((d-1)*c for d,c in h.items())
    new=Q-p['old_questions'];sync=V+new
    # A concrete fixed-width layout. Both side question/answer arrays are included;
    # rules are shared. Extra 1 GiB covers sparse rows, words, FMS and work buffers.
    layout={'question_records_64bytes_both_sides':128*Q,'answer_payload_uint64_both_sides':p['uint64_answer_payload_bytes_two_parties'],'binding_records_4_uint64':32*binding,'synchrony_uint64':8*sync,'orthogonality_4_uint64':32*(joints+p['projection_rows']),'row_slots_2_uint64':16*sum(d*c for d,c in h.items()),'row_headers_4_uint64':32*p['projection_rows'],'reserved_sparse_core_and_work_buffers':1024**3}
    results[directory]={'uniform_pair_probability':str(F(1,Q**2)),'distribution_sum':str(Q**2*F(1,Q**2)),'row_loss_constant_denominator':11616*Q**2,'truncations':levels,'bindings':binding,'synchrony':sync,'joint_graph_tests':joints,'layout_bytes':layout,'layout_total_bytes':sum(layout.values()),'schema_wellformedness':'By indexed range construction, not by enumeration of game pairs. No full-game predicate was serialized or audited.','scalar_pair_rule_parity':'kernel bit basis pivot construction has n-1 independent vectors perpendicular to j; all masks select valid outcome bits.'}
results['elapsed_seconds']=time.perf_counter()-start
results['peak_working_set_bytes']=__import__('runpy').run_path(str(O/'memory.py'))['peak']()
(O/'exact_checks.json').write_text(json.dumps(results,indent=2),encoding='utf-8');print(json.dumps(results,indent=2))
