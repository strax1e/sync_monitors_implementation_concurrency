#include "ltl-check.pml"

typedef POS {
  int firstSenderId;                  // first p_x
  int senderId;                       // p_x
  int neighbors[PROCESSES_AMOUNT];    // neighbors_x
  int neighborsSize;                  // len(neighbors_x)
}

#define isEmpty(channels, index) (empty(channels.inner[index]))
#define isNotEmpty(channels, index) (nempty(channels.inner[index]))

typedef ChannelsArray {
  chan inner[PROCESSES_AMOUNT] = [MAX_CHAN_SIZE] of {POS};
};

typedef ChannelsIntArray {
  chan inner[PROCESSES_AMOUNT] = [MAX_CHAN_SIZE] of {int};
};

inline getMessage(target, channels, index) {
  channels.inner[index] ? target;
}

inline sendPosMessage(source, channels, index) {
  atomic {
    printf("send - to [%d], message = POS(firstSenderId = %d, senderId = %d, neighborsSize = %d)\n", index, source.firstSenderId, source.senderId, source.neighborsSize);
    addNewMessageToLtlArray(source, index)
    channels.inner[index] ! source;
  }
}

inline sendStartMessage(source, channels, index) {
  atomic {
    printf("send - to [%d], message = START\n", index);
    channels.inner[index] ! source;
  }
}

active proctype fakeProcess1() {
  printf("");
}