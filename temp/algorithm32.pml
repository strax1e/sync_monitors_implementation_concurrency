#include "channels-array.pml"
#define START 1001

typedef Pair {
  int first;
  int second;
}

typedef Process {
  int id;
  bool part;

  int neighbors[PROCESSES_AMOUNT];
  int procknown[PROCESSES_AMOUNT];
  Pair chanknown[MAX_CHANNELS_COUNT_BETWEEN_PROCESSES];

  int neighborsSize;
  int procknownSize;
  int chanknownSize;
};

ChannelsArray channelsWithPosMessage;
ChannelsIntArray channelsWithStartMessage;
Process processes[PROCESSES_AMOUNT];
bool everyoneKnowsAllProcesses = false;
bool resultsPrinted = false;

inline printProcess(process) {
  printf("Process(id=%d, part=%d, neighbors[%d]={ ", process.id, process.part, process.neighborsSize);

  int r;
  for (r : 0.. (process.neighborsSize - 1)) {
    printf("%d ", process.neighbors[r]);
  }

  printf("}, procknown[%d]={ ", process.procknownSize);

  for (r : 0.. (process.procknownSize - 1)) {
    printf("%d ", process.procknown[r]);
  }

  printf("}, chanknown[%d]={ ", process.chanknownSize);

  for (r : 0.. (process.chanknownSize - 1)) {
    printf("[%d, %d] ", process.chanknown[r].first, process.chanknown[r].second);
  }

  printf("})\n");
}

inline fillPosMessage(pos, process) {
  pos.senderId = process.id;
  pos.neighborsSize = process.neighborsSize;

  int j;
  for (j : 0..(process.neighborsSize - 1)) {
    pos.neighbors[j] = process.neighbors[j];
  }
}

inline fillPosMessageWithFirstSender(pos, process, _firstSenderId) {
  fillPosMessage(pos, process);
  pos.firstSenderId = _firstSenderId;
}

inline sendInfoAboutCurrentProcessToNeighbors(process) {
  int i;
  for (i : 0..(process.neighborsSize - 1)) {
    int targetProcessId = process.neighbors[i];
    POS pos;
    fillPosMessageWithFirstSender(pos, process, process.id);
    sendPosMessage(pos, channelsWithPosMessage, targetProcessId);
  }
}

inline start(process) {
  printf("start() for process with id [%d]\n", process.id);
  sendInfoAboutCurrentProcessToNeighbors(process);
  process.part = true;
}

inline safetyStart(process) {
  if 
  :: (!process.part) -> 
    start(process);
  :: else
  fi
}

inline startMessageListener(process) {
  if
  :: isNotEmpty(channelsWithStartMessage, process.id) ->
    printf("startMessageListener() for process with id [%d]\n", process.id);
    getMessage(START, channelsWithStartMessage, process.id);
    safetyStart(process);
  :: isEmpty(channelsWithStartMessage, process.id)
  fi;
}

inline procknownContains(result, process, targetId) {
  atomic {
    result = false
    int j;
    for (j : 0..(process.procknownSize - 1)) {
      if
      :: (process.procknown[j] == targetId) -> 
        result = true;
        break;
      :: else
      fi;
    }
  }
}

inline addForeignProcessIdToCurrentProcess(targetProcess, recievedMessage) {
  targetProcess.procknown[targetProcess.procknownSize] = recievedMessage.firstSenderId;
  targetProcess.procknownSize++;
}

inline addForeignNeighborsToCurrentProcess(targetProcess, recievedMessage) {
  int i;
  for (i : 0..(recievedMessage.neighborsSize - 1)) {
    int chanknownIndex = targetProcess.chanknownSize;
    targetProcess.chanknown[chanknownIndex].first = recievedMessage.firstSenderId;
    targetProcess.chanknown[chanknownIndex].second = recievedMessage.neighbors[i];
    targetProcess.chanknownSize++;
  }
}

inline copyPosMessage(source, target) {
  target.firstSenderId = source.firstSenderId;
  target.senderId = source.senderId;
  target.neighborsSize = source.neighborsSize;

  int p;
  for (p : 0.. source.neighborsSize) {
    target.neighbors[p] = source.neighbors[p];
  }
}

inline resendRecievedMessageToNeighbors(process, recievedMessage) {
  int k;
  for (k : 0..(process.neighborsSize - 1)) {
    if 
    :: (recievedMessage.senderId != k) ->
      POS copiedMessage;
      copyPosMessage(recievedMessage, copiedMessage);
      copiedMessage.senderId = process.id;
      sendPosMessage(copiedMessage, channelsWithPosMessage, k);
    :: else
    fi;
  }
}

inline existsUnknownProcess(result, process) {
  result = false;
  int i;
  for (i : 0..(process.chanknownSize - 1)) {
    bool tempResult1 = false;
    bool tempResult2 = false;
    procknownContains(tempResult1, process, process.chanknown[i].first);
    procknownContains(tempResult2, process, process.chanknown[i].second);
    
    if
    :: (!tempResult1 || !tempResult2)
      result = true;
      break;
    :: else
    fi;
  }
}

inline posMessageListener(process) {
  if
  :: isNotEmpty(channelsWithPosMessage, process.id) ->
    printf("posMessageListener() for process with id [%d]\n", process.id);
    safetyStart(process);

    POS recievedMessage;
    getMessage(recievedMessage, channelsWithPosMessage, process.id);

    bool isOnlyKnownProcesses = true;
    procknownContains(isOnlyKnownProcesses, process, recievedMessage.firstSenderId)

    if
    :: !isOnlyKnownProcesses ->
      addForeignProcessIdToCurrentProcess(process, recievedMessage);
      addForeignNeighborsToCurrentProcess(process, recievedMessage);
      resendRecievedMessageToNeighbors(process, recievedMessage);

      atomic {
        bool existsUnknownProcessVar = false;
        existsUnknownProcess(existsUnknownProcessVar, process);

        if
        :: !existsUnknownProcessVar-> 
          everyoneKnowsAllProcesses = true;
          if
          :: !resultsPrinted ->
            resultsPrinted = true;
            printProcknown(process);
            printChanknown(process);
            printLTLResult();
          :: else
          fi;
        :: else
        fi;
      }

    :: else
    fi
  :: isEmpty(channelsWithPosMessage, process.id)
  fi;
}

inline printProcknown(process) {
  printf("\n\nAnswer:\n");
  atomic {
    printf("Procknown for process with id [%d]: { ", process.id);
    int i;
    for (i : 0..(process.procknownSize - 1)) {
      printf("%d ", process.procknown[i]);
    }
    printf("}\n");
  }
}

inline printChanknown(process) {
  atomic {
    printf("Chanknown for process with id [%d]: { ", process.id);
    int i;
    for (i : 0..(process.chanknownSize - 1)) {
      int first = process.chanknown[i].first;
      int second = process.chanknown[i].second;
      printf("[%d, %d] ", first, second);
    }
    printf("}\n");
  }
}

inline printLTLResult() {
  printf("onlyUniqueMessages: ");
  if
  :: wasOnlyUniqueMessages ->
    printf("True\n");
  :: else ->
    printf("False\n");
  fi;
  printf("\n\n");
}

inline copyProcess(source, target) {
  target.id = source.id;
  target.part = source.part;
  target.neighborsSize = source.neighborsSize;
  target.procknownSize = source.procknownSize;
  target.chanknownSize = source.chanknownSize;
  
  int i;
  for (i : 0..(source.neighborsSize - 1)) {
    target.neighbors[i] = source.neighbors[i];
  }
  for (i : 0..(source.procknownSize - 1)) {
    target.procknown[i] = source.procknown[i];
  }
  for (i : 0..(source.chanknownSize - 1)) {
    target.chanknown[i].first = source.chanknown[i].first;
    target.chanknown[i].second = source.chanknown[i].second;
  }
}

proctype main(int index) {
  Process currentProcess;
  copyProcess(processes[index], currentProcess);
  printf("Running process with id [%d]\n", currentProcess.id);

  do
  :: !everyoneKnowsAllProcesses ->
    startMessageListener(currentProcess);
    posMessageListener(currentProcess);
  :: else -> break;
  od;
  
  printf("Stopping process with id [%d]\n", currentProcess.id);
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

  printProcess(processes[0]);
  printProcess(processes[1]);
  printProcess(processes[2]);
  printProcess(processes[3]);

  sendStartMessage(START, channelsWithStartMessage, 1);

  run main(processes[0].id);
  run main(processes[1].id);
  run main(processes[2].id);
  run main(processes[3].id);
}