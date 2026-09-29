# compare_certs.sage: blind comparison (run after the own results were committed, commit aaacbb2) of the sage3 values
# with the PARI certified outputs code/earlier-computations/data/centres_twist<k>.txt ([disc, X0, level, nu, class, inW, vM, ok,
# nu_pari]) and the heuristic values written in the verdicts of code/earlier-computations/data/boxes_twist<k>.txt.
# Classes are coordinates in basis dependent projections: compared through basis free statements only (class in
# pr(W); all classes of a twist equal; equal to the class e1 of pr c_1 at the known lifts).
load('exact_data.sage')
import re
CEN = load('centres_prec1000.sobj')
for k in [0, 1]:
    print('==== twist k = %d ====' % k)
    mine = {(o['disc'], o['X0'], o['level']): o for o in CEN[k]}
    vm = {}
    for line in open('box_bounds_twist%d.txt' % k):
        if line.startswith('#'):
            continue
        v = sage_eval(line.replace('True', '1').replace('False', '0').replace('None', '-1'))
        vm[(v[0], v[1], v[2])] = v
    pari_rows = [sage_eval(l) for l in open('../../earlier-computations/data/centres_twist%d.txt' % k) if l.strip()]
    print(' PARI rows %d, own constant boxes %d' % (len(pari_rows), len(mine)))
    bad = 0
    pcls = set();
    for r in pari_rows:
        key = (r[0], r[1], r[2])
        o = mine.get(key)
        if o is None:
            print('  box %s missing on the Sage side' % (key,)); bad += 1; continue
        pcls.add(tuple(r[4]))
        issues = []
        if r[3] != o['nu0']: issues.append('nu0 PARI %d, Sage %d' % (r[3], o['nu0']))
        if bool(r[5]) != o['inW']: issues.append('inW PARI %d, Sage %s' % (r[5], o['inW']))
        if r[6] != vm[key][4]: issues.append('vM PARI %d, Sage %d' % (r[6], vm[key][4]))
        if r[7] != 1 or vm[key][7] != 1: issues.append('ok PARI %d, Sage %d' % (r[7], vm[key][7]))
        if r[8] != r[3]: issues.append('PARI certified nu %d != its heuristic %d' % (r[3], r[8]))
        if issues:
            bad += 1; print('  box %s: %s' % (key, '; '.join(issues)))
    print(' per box: nu0, "in pr(W)", vM, criterion: %d disagreements over %d boxes' % (bad, len(pari_rows)))
    print(' PARI classes (PARI basis): %s; Sage classes (Sage basis): %s' % (sorted(pcls), sorted(set(tuple(o['cl']) for o in CEN[k]))))
    print(' basis free: PARI: one class for all centres of the twist: %s; Sage: one class, equal to e1 at both known lifts: %s'
          % (len(pcls) == 1, all(o['eqe1'] for o in CEN[k])))
    # box list verdicts (heuristic nu and vM of p21_41)
    bl = s3_boxes(k); badb = 0
    for b in bl:
        v = b['verdict']; key = (b['disc'], b['X0'], b['level'])
        mv = re.search(r'vM = (\d+)', v)
        if v.startswith('constant'):
            nu = int(re.search(r'nu = (\d+)', v).group(1))
            if nu != mine[key]['nu0'] or int(mv.group(1)) != vm[key][4]:
                badb += 1; print('  box list %s: nu %d vM %s vs Sage nu0 %d vM %d' % (key, nu, mv.group(1), mine[key]['nu0'], vm[key][4]))
        elif v.startswith('tail'):
            if int(mv.group(1)) != vm[key][4]:
                badb += 1; print('  box list tail %s: vM %s vs Sage %d' % (key, mv.group(1), vm[key][4]))
    print(' box list verdicts (heuristic nu at centres, vM at constant and tail boxes): %d disagreements over %d constant and tail boxes'
          % (badb, len([b for b in bl if not b['verdict'].startswith('excluded')])))
