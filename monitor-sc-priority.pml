// SC Monitor, signal() and signalAll() is useless while queue is empty

#include "monitor-base.pml"

BlockingQueue purgatory = [0] of { bit };
int inPurgatoryCount = 0;
int pendingSignals = 0;

inline waitBase(condition, number) {
	hash = hash - number;
	inCritSection--;

	waiters++;
	// printf("wait %d\n", number);
	atomic {
		release(outerLock, number, 'l');
		acquire(condition, number, 'c'); // wait()		
		acquire(outerLock, number, 'l');
	}
	printf("awake %d\n", number);

	inCritSection++;
	hash = hash + number;
}

inline waitPurgatory(number) {
	inPurgatoryCount++;

	// printf("wait %d\n", number);
	atomic {
		release(outerLock, number, 'l');
		acquire(purgatory, number, 'c'); // wait()
		acquire(outerLock, number, 'l');
	}
	printf("awake %d\n", number);

	inPurgatoryCount--;
}

inline wait(condition, number) {
	if
	:: (pendingSignals == 0 && inPurgatoryCount > 0) ->
		signalPurgatory(number);
	:: else
	fi

	waitBase(condition, number);

	pendingSignals--;
}

inline signalPurgatory(number) {
	release(purgatory, number, 'c'); // signal()
}

inline signal(condition, number) {
	if
	:: (waiters > 0) ->
		pendingSignals++;
		awakeThread(condition, number);
	:: else -> 
		printf("%d signal() else\n", number);
	fi;
}

inline signalAll(condition, number) {
	if
	:: (waiters > 0) ->
		int waitersCopy = waiters;
		int i;
		for (i : 1.. waitersCopy) {
			pendingSignals++;
			awakeThread(condition, number);
		}
	:: else -> 
		printf("%d signalAll() else\n", number);
	fi;
}

inline enterCriticalSection(number) {
	atomic { hash = hash + number; }
	acquire(outerLock, number, 'l');

	if
	:: (pendingSignals > 0 || inPurgatoryCount > 0) -> 
		waitPurgatory(number);
	:: else
	fi;

	inCritSection++;
}

inline exitCriticalSection(number) {
	if
	:: (pendingSignals == 0 && inPurgatoryCount > 0) ->
		signalPurgatory(number);
	:: else
	fi;

	inCritSection--;

	release(outerLock, number, 'l');
	printf("%d exit\n", number);
	atomic { hash = hash - number; }
}

proctype model(int number) {
	enterCriticalSection(number);

	if
	:: (waiters < 2) ->
		wait(blockingQueue, number);
	:: else ->
		signalAll(blockingQueue, number);
	fi;

	exitCriticalSection(number);
}

inline initMonitor() {
	release(outerLock, 0, 'l'); // init outerLock
}

init {
	initMonitor();
	start(6);
}
