// SW monitor, signal() and signalAll() is useless while queue is empty

#include "monitor-base.pml"

#define Synchronizer chan

Lock innerLock = [1] of { bit };
Synchronizer synchronizer = [0] of { bit };

int awakenedCount = 0;

inline receiveLocks(number) {
	acquire(innerLock, number, 'i');
	acquire(synchronizer, number, 's');
	acquire(outerLock, number, 'o');
}

inline transferLocksToAwakened(number) {
	release(innerLock, number, 'i');
	release(synchronizer, number, 's');
	release(outerLock, number, 'o');
}

inline wait(condition, number) {
	atomic { hash = hash - number; } // for ltl
	inCritSection--;

	waiters++;
	release(outerLock, number, 'o');

	printf("%d going to wait\n", number);
	atomic {
		release(innerLock, number, 'i');
		acquire(condition, number, 'b'); // wait()
	}

	receiveLocks(number);
	awakenedCount--;

	inCritSection++;
	atomic { hash = hash + number; }
}

inline signal(condition, number) {
	atomic { hash = hash - number; }
	inCritSection--;

	if
	:: (waiters > 0) ->
		awakeThread(condition, number);
		transferLocksToAwakened(number);

		acquireSynchronized(number);
	:: else -> 
		printf("%d signal() else\n", number);
	fi;

	inCritSection++;
	atomic { hash = hash + number; }
}

inline signalAll(condition, number) {
	atomic { hash = hash - number; }
	inCritSection--;

	if
	:: (waiters > 0) ->
		awakenedCount = awakenedCount + waiters;
		awakeAllThreads(condition, number);
		transferLocksToAwakened(number);

		acquireSynchronized(number);
	:: else -> 
		printf("%d signalAll() else\n", number);
	fi;

	inCritSection++;
	atomic { hash = hash + number; }
}

inline acquireSynchronized(number) {
	do 
	:: true -> 
		acquire(outerLock, number, 'o');
		atomic { 
			if
			:: nempty(innerLock) -> 
				acquire(innerLock, number, 'i');
				break; 
			:: empty(innerLock) -> 
				skip;
			fi;
		}
		release(outerLock, number, 'o');
	od
}

inline releaseLocks(number) {
	release(innerLock, number, 'i');
	release(outerLock, number, 'o');
}

inline releaseSynchronized(number) {
	if
	:: (awakenedCount > 0) ->
		transferLocksToAwakened(number);
	:: else ->
		releaseLocks(number);
	fi;
}

inline exitCriticalSection(number) {
	inCritSection--;

	releaseSynchronized(number);
	atomic { hash = hash - number; }
}

inline enterCriticalSection(number) {
	atomic { hash = hash + number; }
	acquireSynchronized(number);

	inCritSection++;
}

proctype model(int number) {
	do
	:: true ->
		enterCriticalSection(number);

		if
		:: (waiters < 2) ->
			wait(blockingQueue, number);
		:: else ->
			signalAll(blockingQueue, number);
		fi;

		exitCriticalSection(number);
	od
}

inline initMonitor() {
	release(outerLock, 0, 'o'); // init outerLock
	release(innerLock, 0, 'i'); // init innerLock
}

init {
	initMonitor();
	start(6);
}

/* signalAll(), 7 threads, exclusiveAccess
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
		never claim             + (exclusiveAccess)
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

/* signal(), 9 threads, exclusiveAccess
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
		never claim             + (exclusiveAccess)
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

/* 7 threads, starvationFree
ltl free: <> ([] ((hash==0)))
warning: never claim + accept labels requires -a flag to fully verify
Depth=     645 States=    1e+06 Transitions= 3.68e+06 Memory=   233.417 t=     4.19 R=   2e+05
Depth=    1046 States=    2e+06 Transitions=  7.6e+06 Memory=   340.155 t=     9.54 R=   2e+05
Depth=    1046 States=    3e+06 Transitions= 1.13e+07 Memory=   453.730 t=     12.5 R=   2e+05
Depth=    1046 States=    4e+06 Transitions= 1.49e+07 Memory=   568.183 t=     15.3 R=   3e+05
Depth=    1046 States=    5e+06 Transitions= 1.85e+07 Memory=   682.733 t=       18 R=   3e+05
Depth=    1046 States=    6e+06 Transitions= 2.21e+07 Memory=   793.964 t=     20.6 R=   3e+05
Depth=    1046 States=    7e+06 Transitions= 2.67e+07 Memory=   908.417 t=     25.2 R=   3e+05
Depth=    1046 States=    8e+06 Transitions= 3.16e+07 Memory=  1022.284 t=     33.9 R=   2e+05
Depth=    1046 States=    9e+06 Transitions= 3.61e+07 Memory=  1136.444 t=     41.5 R=   2e+05
Depth=    1046 States=    1e+07 Transitions= 4.09e+07 Memory=  1250.897 t=     50.5 R=   2e+05
Depth=    1112 States=  1.1e+07 Transitions= 4.55e+07 Memory=  1365.448 t=     59.3 R=   2e+05
Depth=    1112 States=  1.2e+07 Transitions= 4.98e+07 Memory=  1479.901 t=     66.2 R=   2e+05
Depth=    1112 States=  1.3e+07 Transitions= 5.46e+07 Memory=  1594.062 t=     74.3 R=   2e+05
Depth=    1922 States=  1.4e+07 Transitions= 5.93e+07 Memory=  1708.515 t=     82.1 R=   2e+05
Depth=    1922 States=  1.5e+07 Transitions= 6.34e+07 Memory=  1822.772 t=     85.4 R=   2e+05
Depth=    1922 States=  1.6e+07 Transitions= 6.76e+07 Memory=  1937.030 t=     88.9 R=   2e+05
Depth=    1922 States=  1.7e+07 Transitions= 7.16e+07 Memory=  2051.386 t=     93.6 R=   2e+05
Depth=    1922 States=  1.8e+07 Transitions= 7.57e+07 Memory=  2165.839 t=      101 R=   2e+05

(Spin Version 6.5.1 -- 3 June 2021)
		+ Partial Order Reduction

Full statespace search for:
		never claim             + (starvationFree)
		assertion violations    + (if within scope of claim)
		acceptance   cycles     - (not selected)
		invalid end states      - (disabled by never claim)

State-vector 136 byte, depth reached 1922, errors: 0
 18963418 states, stored
 60451470 states, matched
 79414888 transitions (= stored+matched)
  3442770 atomic steps
hash conflicts:  16210837 (resolved)

Stats on memory usage (in Megabytes):
 2965.928       equivalent memory usage for states (stored*(State-vector + overhead))
 2148.634       actual memory usage for states (compression: 72.44%)
				state-vector as stored = 91 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
	0.534       memory used for DFS stack (-m10000)
 2276.190       total actual memory usage


unreached in proctype model
		(0 of 96 states)
unreached in init
		(0 of 15 states)
unreached in claim free
		_spin_nvr.tmp:10, state 13, "-end-"
		(1 of 13 states)

pan: elapsed time 106 seconds
pan: rate 178917.05 states/second
*/