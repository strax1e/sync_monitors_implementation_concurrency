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
    do
    ::
        synchronized(number);
    od
}

#ifdef LTL
ltl asdsa { always (inCritSection > 1) }
#endif

init {
    lock ! SEED;
    int initial = 19 * 17;

    int i;
    for (i : 1.. 254) {
        initial = (initial * 31) % 100 + 1;
        run model(initial);
    } 
}
