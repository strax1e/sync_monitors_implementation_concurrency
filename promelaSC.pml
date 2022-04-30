#define SEED 1
#define THREADS_COUNT 6

#define down(monitor) { monitor ? SEED }
#define up(monitor) { monitor ! SEED }

#define Monitor chan

Monitor monitor = [1] of { bit };
chan lock = [1] of { bit }; // взаимноисключающий доступ для крит. секции
int waiters = 0;

inline wait(monitor, number) {
    waiters++;
    atomic {
        lock ! SEED;
        printf("%d release lock before wait\n", number);
        printf("wait %d\n", number);
        monitor ? SEED; // wait()
        waiters--; // in atomic only for signalAll()
    }
    printf("awake %d\n", number);
    
    atomic { lock ? SEED; printf("%d got lock\n", number); }
}

inline signal(monitor, number) {
    if
    :: (waiters > 0) ->
        atomic { monitor ! SEED; printf("signal %d\n", number); } // signal()
    :: else -> 
        printf("%d signal else\n", number);
    fi
}

inline signalAll(monitor, number) {
    int waitersCopy = waiters;
    int i;
    for (i : 1.. waitersCopy) {
        signal(monitor, number);
    }
}


int inCritSection = 0;
// SC Monitor, signal is useless while queue is empty
inline synchronized(number) {
    atomic { lock ? SEED; printf("%d got lock\n", number); }
    // critical section start
    inCritSection++;

    if
    :: (number % 2) ->
        inCritSection--;
        wait(monitor, number);
        inCritSection++;
    :: else ->
        signalAll(monitor, number);
    fi
    
    inCritSection--;
    // critical section end
    atomic { lock ! SEED; printf("%d release lock end\n", number); }
}

proctype model(int number) {
    synchronized(number);
}

#ifdef LTL
ltl invariant { []!(inCritSection > 1) }
#endif

init {
    lock ! SEED;
    int initial = 19 * 17;

    int i;
    for (i : 1.. 8) {
        initial = (initial * 31) % 100 + 1;
        run model(initial);
    } 
}

/*
ltl invariant: [] (! ((inCritSection>1)))
Depth=     255 States=    1e+06 Transitions= 1.34e+06 Memory=   273.749 t=     2.85 R=   4e+05
Depth=     255 States=    2e+06 Transitions= 2.67e+06 Memory=   423.944 t=     5.72 R=   3e+05
Depth=     255 States=    3e+06 Transitions= 3.98e+06 Memory=   579.413 t=     9.05 R=   3e+05
Depth=     255 States=    4e+06 Transitions= 5.33e+06 Memory=   733.515 t=     12.3 R=   3e+05

(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             + (invariant)
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