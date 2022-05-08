#include "monitor-sc.pml"

#define THREADS_COUNT 6
#define MAX_SIZE 2

int queue[MAX_SIZE];
int size = 0;

/**
 *   Blocking LIFO
 */
inline add(number) {
    enterCriticalSection(number);

    do
    :: (size == MAX_SIZE) ->
        wait(blockingQueue, number);
    :: else -> break;
    od;

    queue[size] = number;
    size++;
    printf("%d added at %d\n", number, size)
    signal(blockingQueue, number);

    exitCriticalSection(number);
}

inline remove(number) {
    enterCriticalSection(number);

    do
    :: (size == 0) ->
        wait(blockingQueue, number);
    :: else -> break;
    od;

    size--;
    printf("removed: %d\n", queue[size])
    signal(blockingQueue, number);

    exitCriticalSection(number);
}

proctype adder(int number) {
    add(number);
}

proctype remover(int number) {
    remove(number);
}

init {
    initMonitor();

    int i;
    for (i : 1.. THREADS_COUNT) {
        if
        :: i % 2 -> run adder(i);
        :: else  -> run remover(i);
        fi
    }
}

ltl structInvariant { always (size >= 0 && size <= MAX_SIZE) };
ltl modelInvariant { eventually always (size == 0 && size <= THREADS_COUNT / 2) }
