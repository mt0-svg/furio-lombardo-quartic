# precision_check.sage: empirical check of the claimed precisions (Sage propagation plus the hand-set tail and Hensel
# bounds): the logs computed at PREC 400 must agree with those at PREC 1000 to the precision claimed at PREC 400.
A = load('logs_prec400.sobj'); B = load('logs_prec1000.sobj')
worst = None
for k in [0, 1]:
    for lab, va, vb in zip(['D%d' % (i + 1) for i in range(7)] + ['phi_a', 'phi_b'],
                           A[k]['logD'] + [A[k]['logphi'][A[k]['ia']], A[k]['logphi'][A[k]['ib']]],
                           B[k]['logD'] + [B[k]['logphi'][B[k]['ia']], B[k]['logphi'][B[k]['ib']]]):
        for c in range(2):
            ma = min(3 * va[3 * c + j][1] + j for j in range(3))
            dv = min((3 * (QQ(va[3 * c + j][0]) - QQ(vb[3 * c + j][0])).valuation(2) + j) if QQ(va[3 * c + j][0]) != QQ(vb[3 * c + j][0]) else 10^6 for j in range(3))
            slack = dv - ma
            worst = slack if worst is None else min(worst, slack)
            print(' k = %d, log %-6s component %d: claimed precision at PREC 400 pi^%d, agreement with PREC 1000 pi^%s, consistent: %s' % (k, lab, c, ma, dv, dv >= ma))
print('least (agreement - claimed precision) = %s' % worst)
