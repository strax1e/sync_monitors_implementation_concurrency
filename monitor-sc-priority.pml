// SC Monitor, signal() and signalAll() is useless while queue is empty

#include "monitor-base.pml"

BlockingQueue purgatory = [0] of { bit };
int inPurgatoryCount = 0;
int pendingSignals = 0;

inline waitBase(condition, number) {
	atomic { hash = hash - number; }
	inCritSection--;

	printf("%d going to wait\n", number);
	waiters++;
	atomic {
		release(outerLock, number, 'l');
		acquire(condition, number, 'c'); // wait()		
		acquire(outerLock, number, 'l');
	}
	printf("%d awoke\n", number);

	inCritSection++;
	atomic { hash = hash + number; }
}

int countOfPendingSignalsAfterPurgatory = 0; // always must be zero

inline waitPurgatory(number) {
	inPurgatoryCount++;

	printf("%d going to wait in purgatory\n", number);
	atomic {
		release(outerLock, number, 'l');
		acquire(purgatory, number, 'c'); // wait()
		acquire(outerLock, number, 'l');
	}
	printf("%d awoke from purgatory\n", number);

	inPurgatoryCount--;

	countOfPendingSignalsAfterPurgatory = countOfPendingSignalsAfterPurgatory + pendingSignals;
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
	printf("%d going to signal purgatory\n", number);
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

ltl purgatoryInvariant { always (countOfPendingSignalsAfterPurgatory == 0) };
