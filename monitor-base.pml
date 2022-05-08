#define SEED 1
#define BlockingQueue chan
#define Lock chan

BlockingQueue blockingQueue = [0] of { bit };
Lock outerLock = [1] of { bit }; // взаимноисключающий доступ для крит. секции

int waiters = 0;

int inCritSection = 0;
int hash = 0; 

ltl exclusiveAccess { always (inCritSection == 1 || inCritSection == 0) }
ltl starvationFree { eventually always (hash == 0) }

inline acquire(channel, number, name) {
	atomic {
		channel ? SEED;
		printf("%d acquired %c\n", number, name);
	}
}

inline release(channel, number, name) {
	atomic {
		channel ! SEED;
		printf("%d released %c\n", number, name);
	}
}

inline awakeThread(condition, number) {
	release(condition, number, 'c'); // signal()
	waiters--;
	printf("%d signal\n", number);
}

inline awakeAllThreads(condition, number) {
	int waitersCopy = waiters;
	int i;
	for (i : 1.. waitersCopy) {
		awakeThread(condition, number);
	}
}

inline start(threadsCount) {
	int i;
	for (i : 1.. threadsCount) {
		run model(i);
	}
}
