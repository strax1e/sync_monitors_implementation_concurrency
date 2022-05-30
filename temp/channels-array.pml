#include "ltl-check.pml"

typedef POS {
  int firstSenderId;  // first p_x
  int senderId;       // p_x
  int neighbors[N];   // neighbors_x
  int neighborsSize;  // len(neighbors_x)
}

#define isEmpty(channels, index) (empty(channels.inner[index]))
#define isNotEmpty(channels, index) (nempty(channels.inner[index]))

typedef ChannelsArray {
  chan inner[N] = [MAX_CHAN_SIZE] of {POS};
};

inline getMessage(target, channels, index) {
  channels.inner[index] ? target;
}

inline sendPosMessage(source, channels, index) {
  addNewMessageToLtlArray(source, index)
  channels.inner[index] ! source;
}

inline sendStartMessage(source, channels, index) {
  channels.inner[index] ! source;
}