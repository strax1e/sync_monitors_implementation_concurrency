#define N 10

typedef POS {
  int id;
  int neighbors[N];
  int neighborsLen;
}

typedef ChannelsArray {
  chan inner[N] = [100] of {POS};
};

typedef DoubleArray {
  ChannelsArray outer[N];
};

inline get(target, doubleArray, index_i, index_j) {
  doubleArray.outer[index_i].inner[index_j] ? target;
}

inline set(target, doubleArray, index_i, index_j) {
  doubleArray.outer[index_i].inner[index_j] ! target;
}

// active proctype main() {
//   printf("temp started\n")
//   DoubleArray doubleArray;
  
//   set(123, doubleArray, 0, 0);
//   set(101, doubleArray, 0, 1);
//   set(102, doubleArray, 0, 2);

//   int w;
//   for (w : 0..2) {
//     int temp;
//     get(temp, doubleArray, 0, w);
//     printf(" chto-to = %d\n", temp); 
//   }
// }