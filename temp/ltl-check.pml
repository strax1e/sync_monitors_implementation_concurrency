#define MAX_CHAN_SIZE 25
#define PROCESSES_AMOUNT 4
#define MAX_CHANNELS_COUNT_BETWEEN_PROCESSES (PROCESSES_AMOUNT * (PROCESSES_AMOUNT - 1))
#define MAX_LTL_ARRAY_SIZE MAX_CHAN_SIZE

typedef Tuple {
  int firstSenderId = -1;
  int senderId = -1;
  int count = 0;
}

typedef LtlArray {
  Tuple posMessages[MAX_LTL_ARRAY_SIZE];
  int size = 0;
}

LtlArray posMessagesForLtlConstraintCheck[PROCESSES_AMOUNT];
bool wasOnlyUniqueMessages = true;
ltl onlyUniqueMessages { always wasOnlyUniqueMessages }

inline tryToAddOldPosMessage(source, index, isNewPos) {
  int p;
  for (p : 0..posMessagesForLtlConstraintCheck[index].size) {
    int currentFirstSenderId = posMessagesForLtlConstraintCheck[index].posMessages[p].firstSenderId;
    int currentSenderId = posMessagesForLtlConstraintCheck[index].posMessages[p].senderId;
    if
    :: (source.firstSenderId == currentFirstSenderId && source.senderId == currentSenderId) ->
      isNewPos = false;
      posMessagesForLtlConstraintCheck[index].posMessages[p].count++;
      break;
    :: else
    fi;
  }
}

inline tryToAddNewPosMessage(source, index, isNewPos) {
  if
  :: isNewPos ->
    int size = posMessagesForLtlConstraintCheck[index].size;
    posMessagesForLtlConstraintCheck[index].posMessages[size].firstSenderId = source.firstSenderId;
    posMessagesForLtlConstraintCheck[index].posMessages[size].senderId = source.senderId;
    posMessagesForLtlConstraintCheck[index].posMessages[size].count++;
    posMessagesForLtlConstraintCheck[index].size++;
  :: else
  fi;
}

inline addNewMessageToLtlArray(source, index) {
  atomic {
    bool isNewPos = true;
    tryToAddOldPosMessage(source, index, isNewPos);
    tryToAddNewPosMessage(source, index, isNewPos);

    if
    :: !isNewPos ->
      wasOnlyUniqueMessages = false;
    :: else
    fi;
  }
}

active proctype fakeProcess() {
  printf("temp proctype ltl-check");
}