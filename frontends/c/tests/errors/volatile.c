/* volatile isn't in this round. */
int main(void) {
  volatile int flag = 1;
  return flag;
}

// expect: 3:16: 'volatile'
