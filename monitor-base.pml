#define SEED 1
#define BlockingQueue chan
#define Lock chan

BlockingQueue blockingQueue = [0] of { bit };
Lock outerLock = [1] of { bit }; // взаимноисключающий доступ для крит. секции

int waiters = 0;

int inCritSection = 0;
int hash = 0; 

ltl exclusiveAccess { []!(inCritSection > 1) }
ltl starvationFree { <>[](hash == 0) }

inline acquire(channel, number, name) {
    atomic {
        channel ? SEED;
        printf("%d acquire %c\n", number, name);
    }
}

inline release(channel, number, name) {
    atomic {
        channel ! SEED;
        printf("%d release %c\n", number, name);
    }
}

inline awakeThread(number) {
    release(blockingQueue, number, 'b'); // signal()
    printf("%d signal\n", number);
}

inline awakeAllThreads(number) {
	int waitersCopy = waiters;
    int i;
    for (i : 1.. waitersCopy) {
        awakeThread(number);
    }
}

inline start(threadsCount) {
    int i;
    for (i : 1.. threadsCount) {
        run synchronized(i);
    }
}
