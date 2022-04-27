#define SEED 1
#define THREADS_COUNT 6

#define down(monitor) { monitor ? SEED }
#define up(monitor) { monitor ! SEED }

#define Monitor chan

Monitor monitor = [1] of { bit };
chan lock = [1] of { bit }; // взаимноисключающий доступ для крит. секции
chan lock2 = [1] of { bit };
chan blockingQueue = [THREADS_COUNT - 1] of { bit };
int waiters = 0;

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
    printf("awake %d\n", number);
    
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
        :: (nempty(blockingQueue))
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
        :: (nempty(blockingQueue))
        :: empty(blockingQueue) -> break;
        od
        atomic { lock2 ? SEED; printf("%d got lock2\n", number); }
        atomic { lock ? SEED; printf("%d got lock\n", number); }
    :: else -> 
        printf("%d signal else\n", number);
    fi
}

// SW Monitor, signal is useless while queue is empty
proctype synchronized(int number) {
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
    if
    :: (waiters < 2) ->
        wait(monitor, number); // 1 waiting
    :: else ->
        signalAll(monitor, number); // 2 preparing to signal 1
    fi
    // critical section end
    atomic { lock ! SEED; printf("%d release lock end\n", number); }
    atomic { lock2 ! SEED; printf("%d release lock2 end\n", number); }
}

init {
    lock ! SEED;
    lock2 ! SEED;
    int i;
    for (i : 1.. THREADS_COUNT) {
        run synchronized(i);
    } 
}
