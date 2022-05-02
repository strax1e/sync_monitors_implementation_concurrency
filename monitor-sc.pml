// SC Monitor, signal() and signalAll() is useless while queue is empty

#include "monitor-base.pml"

inline wait(blockingQueue, number) {
    waiters++;
    atomic {
        release(outerLock, number, 'l');
        printf("wait %d\n", number);
        acquire(blockingQueue, number, 'b'); // wait()
        waiters--;
    }
    printf("awake %d\n", number);
    
    acquire(outerLock, number, 'l');
}

inline signal(blockingQueue, number) {
    if
    :: (waiters > 0) ->
        awakeThread(number);
    :: else -> 
        printf("%d signal() else\n", number);
    fi;
}

inline signalAll(blockingQueue, number) {
    if
    :: (waiters > 0) ->
        awakeAllThreads(number)
    :: else -> 
        printf("%d signalAll() else\n", number);
    fi;
}

proctype synchronized(int number) {
    atomic { hash = hash + number; }
    acquire(outerLock, number, 'l');

    // critical section start
    inCritSection++;

    if
    :: (waiters < 2) ->
        atomic { hash = hash - number; }
        inCritSection--;
        wait(blockingQueue, number);
        inCritSection++;
        atomic { hash = hash + number; }
    :: else ->
        signalAll(blockingQueue, number);
    fi

    inCritSection--;
    // critical section end

    release(outerLock, number, 'l');
    atomic { hash = hash - number; }
}

init {
    release(outerLock, 0, 'l'); // init outerLock

    start(6);
}

/* signalAll(), 8 threads, exclusiveAccess
ltl invariant: [] (! ((inCritSection>1)))
Depth=     255 States=    1e+06 Transitions= 1.34e+06 Memory=   273.749 t=     2.85 R=   4e+05
Depth=     255 States=    2e+06 Transitions= 2.67e+06 Memory=   423.944 t=     5.72 R=   3e+05
Depth=     255 States=    3e+06 Transitions= 3.98e+06 Memory=   579.413 t=     9.05 R=   3e+05
Depth=     255 States=    4e+06 Transitions= 5.33e+06 Memory=   733.515 t=     12.3 R=   3e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (exclusiveAccess)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 192 byte, depth reached 255, errors: 0
  4272341 states, stored
  1426043 states, matched
  5698384 transitions (= stored+matched)
   159223 atomic steps
hash conflicts:    111218 (resolved)

Stats on memory usage (in Megabytes):
  896.373       equivalent memory usage for states (stored*(State-vector + overhead))
  648.622       actual memory usage for states (compression: 72.36%)
                state-vector as stored = 131 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
  776.581       total actual memory usage


unreached in proctype model
        (0 of 48 states)
unreached in init
        (0 of 14 states)
unreached in claim invariant
        _spin_nvr.tmp:8, state 10, "-end-"
        (1 of 10 states)

pan: elapsed time 13.2 seconds
pan: rate 322928.27 states/second
*/

/* signal(), 12 threads, exclusiveAccess
ltl invariant: [] (! ((inCritSection>1)))
Depth=     321 States=    1e+06 Transitions=  1.6e+06 Memory=   258.026 t=     4.09 R=   2e+05
Depth=     321 States=    2e+06 Transitions= 3.32e+06 Memory=   395.233 t=     9.08 R=   2e+05
Depth=     321 States=    3e+06 Transitions= 5.19e+06 Memory=   530.683 t=       14 R=   2e+05
Depth=     321 States=    4e+06 Transitions= 6.94e+06 Memory=   665.839 t=     18.7 R=   2e+05
Depth=     321 States=    5e+06 Transitions= 8.72e+06 Memory=   803.144 t=     23.9 R=   2e+05
Depth=     321 States=    6e+06 Transitions= 1.04e+07 Memory=   940.448 t=     28.6 R=   2e+05
Depth=     321 States=    7e+06 Transitions= 1.21e+07 Memory=  1077.851 t=     33.5 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (exclusiveAccess)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 160 byte, depth reached 321, errors: 0
  7828883 states, stored
  5713462 states, matched
 13542345 transitions (= stored+matched)
   481542 atomic steps
hash conflicts:    718957 (resolved)

Stats on memory usage (in Megabytes):
 1403.646       equivalent memory usage for states (stored*(State-vector + overhead))
 1063.664       actual memory usage for states (compression: 75.78%)
                state-vector as stored = 114 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
 1191.718       total actual memory usage


unreached in proctype model
        (0 of 37 states)
unreached in init
        (0 of 14 states)
unreached in claim invariant
        _spin_nvr.tmp:8, state 10, "-end-"
        (1 of 10 states)

pan: elapsed time 37.4 seconds
pan: rate 209328.42 states/second
*/

/* 8 threads, starvationFree
pan: ltl formula starvationFree
Depth=     247 States=    1e+06 Transitions= 4.57e+06 Memory=   184.589 t=     4.26 R=   2e+05
Depth=     247 States=    2e+06 Transitions= 9.61e+06 Memory=   241.620 t=      8.7 R=   2e+05
Depth=     247 States=    3e+06 Transitions= 1.52e+07 Memory=   299.042 t=     14.1 R=   2e+05
Depth=     247 States=    4e+06 Transitions= 1.96e+07 Memory=   360.077 t=     18.7 R=   2e+05
Depth=     247 States=    5e+06 Transitions= 2.39e+07 Memory=   421.112 t=     23.2 R=   2e+05
Depth=     247 States=    6e+06 Transitions= 2.82e+07 Memory=   482.147 t=     30.2 R=   2e+05
Depth=     247 States=    7e+06 Transitions= 3.24e+07 Memory=   543.183 t=       39 R=   2e+05
Depth=     265 States=    8e+06 Transitions= 3.72e+07 Memory=   604.218 t=     48.6 R=   2e+05
Depth=     265 States=    9e+06 Transitions= 4.14e+07 Memory=   659.687 t=     57.1 R=   2e+05
Depth=     265 States=    1e+07 Transitions= 4.64e+07 Memory=   717.890 t=     66.3 R=   2e+05
Depth=     265 States=  1.1e+07 Transitions=  5.1e+07 Memory=   779.022 t=     75.7 R=   1e+05
Depth=     265 States=  1.2e+07 Transitions= 5.53e+07 Memory=   839.960 t=     84.6 R=   1e+05
Depth=     265 States=  1.3e+07 Transitions= 6.06e+07 Memory=   900.995 t=     94.6 R=   1e+05
Depth=     265 States=  1.4e+07 Transitions= 6.61e+07 Memory=   962.030 t=      105 R=   1e+05
Depth=     265 States=  1.5e+07 Transitions= 7.14e+07 Memory=  1022.284 t=      115 R=   1e+05
Depth=     265 States=  1.6e+07 Transitions= 7.59e+07 Memory=  1083.026 t=      124 R=   1e+05
Depth=     265 States=  1.7e+07 Transitions= 8.08e+07 Memory=  1143.378 t=      134 R=   1e+05
Depth=     265 States=  1.8e+07 Transitions= 8.64e+07 Memory=  1203.632 t=      145 R=   1e+05
Depth=     265 States=  1.9e+07 Transitions= 9.22e+07 Memory=  1264.081 t=      156 R=   1e+05
Depth=     265 States=    2e+07 Transitions=  9.9e+07 Memory=  1325.116 t=      170 R=   1e+05
Depth=     265 States=  2.1e+07 Transitions= 1.05e+08 Memory=  1386.151 t=      183 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (starvationFree)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 128 byte, depth reached 265, errors: 0
 10789171 states, stored (2.15783e+07 visited)
 88007734 states, matched
1.09586e+08 transitions (= visited+matched)
  1633182 atomic steps
hash conflicts:  15055557 (resolved)

Stats on memory usage (in Megabytes):
 1605.139       equivalent memory usage for states (stored*(State-vector + overhead))
 1293.193       actual memory usage for states (compression: 80.57%)
                state-vector as stored = 98 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
 1421.503       total actual memory usage


unreached in proctype model
        (0 of 45 states)
unreached in init
        (0 of 14 states)
unreached in claim starvationFree
        _spin_nvr.tmp:19, state 13, "-end-"
        (1 of 13 states)

pan: elapsed time 191 seconds
pan: rate 113058.11 states/second
*/
