#define SEED 1
#define THREADS_COUNT 6

#define down(monitor) { monitor ? SEED }
#define up(monitor) { monitor ! SEED }
#define timeout false

#define Monitor chan

Monitor monitor = [1] of { bit };
chan lock = [1] of { bit }; // взаимноисключающий доступ для крит. секции
chan lock2 = [1] of { bit };
chan blockingQueue = [THREADS_COUNT - 1] of { bit };
int waiters = 0;

inline wait(monitor, number) {
    waiters++;
    atomic {
        lock ! SEED;
        printf("%d release lock before wait", number);
    }

    atomic {
        lock2 ! SEED;
        printf("%d release lock2 before wait", number);
        printf("wait %d", number);
        monitor ? SEED; // wait()
        waiters--; // in atomic only for signalAll()
    }
    printf("awake %d", number);
    
    atomic { lock2 ? SEED; printf("%d got lock2", number); }
    blockingQueue ? SEED;
    atomic { lock ? SEED; printf("%d got lock", number); }
    blockingQueue ! SEED;
}

inline signal(monitor, number) {
    if
    :: (waiters > 0) ->
        atomic { monitor ! SEED; printf("%d signal", number); } // signal()

        atomic { lock2 ! SEED; printf("%d release lock2", number); }
        blockingQueue ! SEED;
        atomic { lock ! SEED; printf("%d release lock", number); }

        // blockingQueue ? SEED;
        do
        :: (len(blockingQueue) < THREADS_COUNT - 2)
        :: else -> break;
        od
        atomic { lock ? SEED; printf("%d got lock", number); }
        atomic { lock2 ? SEED; printf("%d got lock2", number); }
    :: else -> 
        printf("%d signal else", number);
    fi
}

inline signalAll(monitor, number) { // TODO
    if
    :: (waiters > 0) ->
        atomic { lock2 ! SEED; printf("%d release lock2", number); }

        int i;
        int waitersCopy = waiters;
        for (i : 1..waitersCopy) {
            atomic { monitor ! SEED; printf("%d signal", number); } // signal()
            blockingQueue ! SEED;
        }
        atomic { lock ! SEED; printf("%d release lock", number); }

        do
        :: (len(blockingQueue) < THREADS_COUNT - 2)
        :: else -> break;
        od
        atomic { lock ? SEED; printf("%d got lock", number); }
        atomic { lock2 ? SEED; printf("%d got lock2", number); }
    :: else -> 
        printf("%d signal else", number);
    fi
}

// SW Monitor, signal is useless while queue is empty
proctype synchronized(int number) {
    do 
    :: true -> 
        atomic { lock ? SEED; printf("%d got lock", number); }
        atomic { 
            if
            :: nempty(lock2) -> 
                atomic { lock2 ? SEED; printf("%d got lock2", number); }
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
    atomic { lock ! SEED; printf("%d release lock end", number); }
    atomic { lock2 ! SEED; printf("%d release lock2 end", number); }
}

init {
    lock ! SEED;
    lock2 ! SEED;
    run synchronized(1);
    run synchronized(2);
    run synchronized(3);
    run synchronized(4);
    run synchronized(5);
    run synchronized(6);
}
