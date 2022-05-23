#include "Arrays.pml"
#define neighborsCount 10
#define START 1001

typedef Pair {
  int first;
  int second;
}

typedef Process {
  int id;
  bool part;
  int neighbors[N];
  int procknown[N];
  Pair chanknown[N];
  int neighborsLen;
  int procknownLen;
  int chanknownLen;
};

DoubleArray channels;

inline start(process) {
  POS neighborsPos;
  neighborsPos.id = process.id;
  neighborsPos.neighborsLen = process.neighborsLen;
  int w;
  for (w : 0..process.neighborsLen) {
    neighborsPos.neighbors[w] = process.neighbors[w];
  }

  for (w : 0.. process.neighborsLen) {
    set(neighborsPos, channels, process.id, process.neighbors[w]);
  }

  process.part = true;
}

chan initChan = [1] of { int };

proctype main(Process process) {
  do
  :: true -> {
    if
    :: nempty(initChan) -> {
      initChan ? START;
      if 
      ::(!process.part) -> start(process);
      :: else
      fi
    }
    :: else
    fi
  }
  :: else -> { }
  od;
}

init {

  Process process1;
  process1.id = 0;
  process1.part = false;
  process1.neighbors[0] = 1;
  process1.neighbors[1] = 2;
  process1.neighbors[2] = 3;
  process1.chanknown[0].first = 0;
  process1.chanknown[0].second = 1;
  process1.chanknown[1].first = 0;
  process1.chanknown[1].second = 2;
  process1.chanknown[2].first = 0;
  process1.chanknown[2].second = 3;

  start(process1);

  printf("id = %d\n", process1.id)
}