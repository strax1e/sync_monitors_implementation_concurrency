#include "channels-array.pml"
#define START 1001
#define PROCESSES_AMOUNT 4

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

  int neighborsSize;
  int procknownSize;
  int chanknownSize;
};

ChannelsArray channelsWithPosMessage;
ChannelsArray channelsWithStartMessage;
Process processes[PROCESSES_AMOUNT];

inline copyProcess(source, target) {
  target.id = source.id;
  target.part = source.part;
  target.neighborsSize = source.neighborsSize;
  target.procknownSize = source.procknownSize;
  target.chanknownSize = source.chanknownSize;
  
  int i;
  for (i : 0..source.neighborsSize) {
    target.neighbors[i] = source.neighbors[i];
  }
  for (i : 0..source.procknownSize) {
    target.procknown[i] = source.procknown[i];
  }
  for (i : 0..source.chanknownSize) {
    target.chanknown[i].first = source.chanknown[i].first;
    target.chanknown[i].second = source.chanknown[i].second;
  }
}

inline fillPosMessage(pos, process) {
  pos.senderId = process.id;
  pos.neighborsSize = process.neighborsSize;

  int j;
  for (j : 0..process.neighborsSize) {
    pos.neighbors[j] = process.neighbors[j];
  }
}

inline fillPosMessageWithFirstSender(pos, process, _firstSenderId) {
  fillPosMessage(pos, process);
  pos.firstSenderId = _firstSenderId;
}

inline sendInfoAboutCurrentProcessToNeighbors(process) {
  int i;
  for (i : 0..process.neighborsSize) {
    int targetProcessId = process.neighbors[i];
    POS pos;
    fillPosMessageWithFirstSender(pos, process, process.id);
    sendMessage(pos, channelsWithPosMessage, targetProcessId);
  }
}

inline start(process) {
  sendInfoAboutCurrentProcessToNeighbors(process);
  process.part = true;
}

inline safetyStart(process) {
  if 
  :: (!process.part) -> start(process);
  :: else
  fi
}

inline startMessageListener(process) {
  if
  :: isNotEmpty(channelsWithStartMessage, process.id) ->
    getMessage(START, channelsWithStartMessage, process.id);
    safetyStart(process);
  :: isEmpty(channelsWithStartMessage, process.id)
  fi;
}

inline posMessageListener(process) {
  if
  :: isNotEmpty(channelsWithPosMessage, process.id) ->
    safetyStart(process);
    // TODO: Main if (7)
  :: isEmpty(channelsWithPosMessage, process.id)
  fi;
}

proctype main(int index) {
  bool allProcessFound = false;
  // TODO: Add allProcessFound++ somewhere

  Process currentProcess;
  copyProcess(processes[index], currentProcess);
  printf("Running process with id [%d]\n", currentProcess.id);

  do
  :: !allProcessFound ->
    startMessageListener(currentProcess);
    posMessageListener(currentProcess);
  :: else -> break;
  od;

  // TODO: Add output with procknown and chanknown
}

init {
  processes[0].id = 0;
  processes[0].part = false;
  processes[0].neighborsSize = 2;
  processes[0].neighbors[0] = 1;
  processes[0].neighbors[1] = 3;
  processes[0].chanknownSize = 2;
  processes[0].chanknown[0].first = 0;
  processes[0].chanknown[0].second = 1;
  processes[0].chanknown[1].first = 0;
  processes[0].chanknown[1].second = 3;
  processes[0].procknownSize = 1;
  processes[0].procknown[0] = processes[0].id;

  processes[1].id = 1;
  processes[1].part = false;
  processes[1].neighborsSize = 3;
  processes[1].neighbors[0] = 0;
  processes[1].neighbors[1] = 2;
  processes[1].neighbors[2] = 3;
  processes[1].chanknownSize = 3;
  processes[1].chanknown[0].first = 1;
  processes[1].chanknown[0].second = 0;
  processes[1].chanknown[1].first = 1;
  processes[1].chanknown[1].second = 2;
  processes[1].chanknown[2].first = 1;
  processes[1].chanknown[2].second = 3;
  processes[1].procknownSize = 1;
  processes[1].procknown[0] = processes[1].id;

  processes[2].id = 2;
  processes[2].part = false;
  processes[2].neighborsSize = 2;
  processes[2].neighbors[0] = 1;
  processes[2].neighbors[1] = 3;
  processes[2].chanknownSize = 2;
  processes[2].chanknown[0].first = 2;
  processes[2].chanknown[0].second = 1;
  processes[2].chanknown[1].first = 2;
  processes[2].chanknown[1].second = 3;
  processes[2].procknownSize = 1;
  processes[2].procknown[0] = processes[2].id;

  processes[3].id = 3;
  processes[3].part = false;
  processes[3].neighborsSize = 3;
  processes[3].neighbors[0] = 0;
  processes[3].neighbors[1] = 1;
  processes[3].neighbors[2] = 2;
  processes[3].chanknownSize = 3;
  processes[3].chanknown[0].first = 3;
  processes[3].chanknown[0].second = 0;
  processes[3].chanknown[1].first = 3;
  processes[3].chanknown[1].second = 1;
  processes[3].chanknown[2].first = 3;
  processes[3].chanknown[2].second = 2;
  processes[3].procknownSize = 1;
  processes[3].procknown[0] = processes[3].id;

  sendMessage(START, channelsWithStartMessage, 1);

  run main(processes[0].id);
  run main(processes[1].id);
  run main(processes[2].id);
  run main(processes[3].id);
}