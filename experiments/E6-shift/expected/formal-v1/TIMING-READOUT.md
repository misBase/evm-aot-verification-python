# E22 completed timing subset

36 fresh unobserved timing points: 30 VERIFIED and 6 TO; 12 predeclared repeats skipped only because exact R1 wall exceeded300s. Original combined STOPPED and its first diagnostic parser error remain unchanged. Separate repaired diagnostics are not timing samples.

| k | off executed / skipped | off median or censor | on executed | on median [min,max] s |
|---:|---:|---:|---:|---:|
| 1 | 3 / 0 | 2.959s | 3 | 4.479 [4.461,4.837] |
| 2 | 3 / 0 | 54.100s | 3 | 5.487 [5.482,5.548] |
| 3 | 1 / 2 | ≥600s (TO) | 3 | 6.733 [6.646,6.794] |
| 4 | 1 / 2 | ≥600s (TO) | 3 | 6.866 [6.864,6.942] |
| 5 | 1 / 2 | ≥600s (TO) | 3 | 7.558 [7.509,7.744] |
| 6 | 1 / 2 | ≥600s (TO) | 3 | 8.169 [8.161,8.213] |
| 7 | 1 / 2 | ≥600s (TO) | 3 | 9.096 [8.987,9.214] |
| 8 | 1 / 2 | ≥600s (TO) | 3 | 10.384 [10.177,10.761] |

Model d213/113, compiler archive b3ddbdb, depth400, whole-point600s/tree6000MiB, each query≤300s, OFF concrete1e9, fixed512-byte symbolic calldata, path-pair1, only shift summary toggled. All executed groups were independently confirmed gone; original144pins unchanged. No owned observer was loaded in timing workers. Shape/primary-path statistics belong to the distinct diagnostic pass.

Raw paths/SHA and full protocol are in TIMING-READOUT.json. Censored points are not completed times, and no universal c^k rate or arbitrary-contract result is inferred.
