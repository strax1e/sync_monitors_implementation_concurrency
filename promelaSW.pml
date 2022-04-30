#define SEED 1
#define THREADS_COUNT 9

#define down(monitor) { monitor ? SEED }
#define up(monitor) { monitor ! SEED }

#define Monitor chan
#define Lock chan

Monitor monitor = [1] of { bit };
Lock lock = [1] of { bit }; // взаимноисключающий доступ для крит. секции
Lock lock2 = [1] of { bit };
chan blockingQueue = [THREADS_COUNT - 1] of { bit };
int waiters = 0;

int inCritSection = 0;

inline wait(monitor, number) {
    waiters++;
    atomic { lock ! SEED; printf("%d release lock before wait\n", number); }

    atomic {
        lock2 ! SEED;
        printf("%d release lock2 before wait\n", number);
        printf("wait %d\n", number);
        monitor ? SEED; // wait()
        waiters--; // in atomic only for signalAll()
    }
    printf("awakened %d\n", number);
    
    atomic { lock2 ? SEED; printf("%d got lock2\n", number); }
    blockingQueue ? SEED;
    atomic { lock ? SEED; printf("%d got lock\n", number); }
}

inline signal(monitor, number) {
    if
    :: (waiters > 0) ->
        atomic { monitor ! SEED; printf("signal %d\n", number); } // signal()

        atomic { lock2 ! SEED; printf("%d release lock2\n", number); }
        blockingQueue ! SEED;
        atomic { lock ! SEED; printf("%d release lock\n", number); }

        do
        :: nempty(blockingQueue)
        :: empty(blockingQueue) -> break;
        od
        atomic { lock2 ? SEED; printf("%d got lock2\n", number); }
        atomic { lock ? SEED; printf("%d got lock\n", number); }
    :: else -> 
        printf("%d signal else\n", number);
    fi
}

inline signalAll(monitor, number) {
    if
    :: (waiters > 0) ->
        atomic { lock2 ! SEED; printf("%d release lock2\n", number); }

        int i;
        int waitersCopy = waiters;
        for (i : 1..waitersCopy) {
            atomic { monitor ! SEED; printf("signal %d\n", number); } // signal()
            blockingQueue ! SEED;
        }
        atomic { lock ! SEED; printf("%d release lock\n", number); }

        do
        :: nempty(blockingQueue)
        :: empty(blockingQueue) -> break;
        od
        atomic { lock2 ? SEED; printf("%d got lock2\n", number); }
        atomic { lock ? SEED; printf("%d got lock\n", number); }
    :: else -> 
        printf("%d signal else\n", number);
    fi
}

// SW Monitor, signal is useless while queue is empty
inline synchronized(number) {
    do 
    :: true -> 
        atomic { lock ? SEED; printf("%d got lock\n", number); }
        atomic { 
            if
            :: nempty(lock2) -> 
                atomic { lock2 ? SEED; printf("%d got lock2\n", number); }
                break; 
            :: empty(lock2) -> 
                skip;
            fi
        }

        atomic { lock ! SEED; }
    od
    // critical section start
    inCritSection++;
    if
    :: (number % 2) ->
        inCritSection--;
        wait(monitor, number);
        inCritSection++;
    :: else ->
        inCritSection--;
        // signalAll(monitor, number);
        signal(monitor, number);
        inCritSection++;
    fi

    inCritSection--;
    // critical section end
    atomic { lock ! SEED; printf("%d release lock end\n", number); }
    atomic { lock2 ! SEED; printf("%d release lock2 end\n", number); }
}

proctype model(int number) {
    synchronized(number);
}

#ifdef LTL
ltl invariant { []!(inCritSection > 1) }
#endif

init {
    lock ! SEED;
    lock2 ! SEED;
    int initial = 19 * 17;

    int i;
    for (i : 1.. THREADS_COUNT) {
        initial = (initial * 31) % 100 + 1;
        run model(initial);
    } 
}

/* signalAll(), 7 threads
ltl invariant: [] (! ((inCritSection>1)))
Depth=     775 States=    1e+06 Transitions= 2.16e+06 Memory=   275.897 t=     2.54 R=   4e+05
Depth=    1168 States=    2e+06 Transitions= 4.26e+06 Memory=   429.901 t=     7.56 R=   3e+05
Depth=    1168 States=    3e+06 Transitions= 6.58e+06 Memory=   585.565 t=       13 R=   2e+05
Depth=    1168 States=    4e+06 Transitions=  8.9e+06 Memory=   741.718 t=     18.8 R=   2e+05
Depth=    1168 States=    5e+06 Transitions= 1.12e+07 Memory=   896.698 t=     24.9 R=   2e+05
Depth=    1168 States=    6e+06 Transitions= 1.35e+07 Memory=  1055.487 t=     30.8 R=   2e+05
Depth=    1168 States=    7e+06 Transitions= 1.59e+07 Memory=  1207.636 t=     36.4 R=   2e+05
Depth=    1168 States=    8e+06 Transitions= 1.82e+07 Memory=  1363.593 t=     42.1 R=   2e+05
Depth=    1168 States=    9e+06 Transitions= 2.06e+07 Memory=  1520.233 t=     48.1 R=   2e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (invariant)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 192 byte, depth reached 1168, errors: 0
  9950949 states, stored
 12942251 states, matched
 22893200 transitions (= stored+matched)
  1218275 atomic steps
hash conflicts:   2042752 (resolved)

Stats on memory usage (in Megabytes):
 2087.792       equivalent memory usage for states (stored*(State-vector + overhead))
 1540.987       actual memory usage for states (compression: 73.81%)
                state-vector as stored = 134 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
    1.242       memory lost to fragmentation
 1668.280       total actual memory usage


unreached in proctype model
        (0 of 94 states)
unreached in init
        (0 of 15 states)
unreached in claim invariant
        _spin_nvr.tmp:8, state 10, "-end-"
        (1 of 10 states)

pan: elapsed time 54.2 seconds
pan: rate 183596.85 states/second
*/

/* signal(), 9 threads
ltl invariant: [] (! ((inCritSection>1)))
Depth=    1056 States=    1e+06 Transitions= 3.07e+06 Memory=   249.530 t=     4.83 R=   2e+05
Depth=    1739 States=    2e+06 Transitions= 6.18e+06 Memory=   371.112 t=     10.7 R=   2e+05
Depth=    1767 States=    3e+06 Transitions=  9.4e+06 Memory=   493.183 t=       17 R=   2e+05
Depth=    3302 States=    4e+06 Transitions= 1.26e+07 Memory=   616.034 t=     22.9 R=   2e+05
Depth=    3302 States=    5e+06 Transitions= 1.55e+07 Memory=   745.331 t=     29.3 R=   2e+05
Depth=    3302 States=    6e+06 Transitions= 1.92e+07 Memory=   874.921 t=     36.7 R=   2e+05
Depth=    3302 States=    7e+06 Transitions= 2.29e+07 Memory=  1003.339 t=     43.9 R=   2e+05
Depth=    3302 States=    8e+06 Transitions= 2.62e+07 Memory=  1133.124 t=     50.5 R=   2e+05
Depth=    3302 States=    9e+06 Transitions= 2.98e+07 Memory=  1262.909 t=     57.8 R=   2e+05
Depth=    3302 States=    1e+07 Transitions= 3.34e+07 Memory=  1392.792 t=     65.5 R=   2e+05
Depth=    3302 States=  1.1e+07 Transitions= 3.69e+07 Memory=  1522.675 t=     73.1 R=   2e+05
Depth=    3302 States=  1.2e+07 Transitions= 4.04e+07 Memory=  1652.460 t=     80.2 R=   1e+05
Depth=    3303 States=  1.3e+07 Transitions= 4.38e+07 Memory=  1782.343 t=       87 R=   1e+05
Depth=    3327 States=  1.4e+07 Transitions= 4.71e+07 Memory=  1912.226 t=     94.2 R=   1e+05
Depth=    3327 States=  1.5e+07 Transitions= 5.06e+07 Memory=  2041.230 t=      101 R=   1e+05
Depth=    3327 States=  1.6e+07 Transitions= 5.41e+07 Memory=  2170.819 t=      109 R=   1e+05
Depth=    3327 States=  1.7e+07 Transitions= 5.77e+07 Memory=  2300.702 t=      116 R=   1e+05
Depth=    3435 States=  1.8e+07 Transitions= 6.12e+07 Memory=  2430.390 t=      125 R=   1e+05
Depth=    3576 States=  1.9e+07 Transitions= 6.48e+07 Memory=  2560.077 t=      133 R=   1e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (invariant)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 160 byte, depth reached 6441, errors: 0
 19652330 states, stored
 47496095 states, matched
 67148425 transitions (= stored+matched)
  4912557 atomic steps
hash conflicts:  11337717 (resolved)

Stats on memory usage (in Megabytes):
 3523.481       equivalent memory usage for states (stored*(State-vector + overhead))
 2518.662       actual memory usage for states (compression: 71.48%)
                state-vector as stored = 106 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    0.534       memory used for DFS stack (-m10000)
    2.451       memory lost to fragmentation
 2644.745       total actual memory usage


unreached in proctype model
        (0 of 84 states)
unreached in init
        (0 of 15 states)
unreached in claim invariant
        _spin_nvr.tmp:8, state 10, "-end-"
        (1 of 10 states)

pan: elapsed time 139 seconds
pan: rate    141618 states/second
*/