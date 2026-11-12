/* GNU computed goto. */
int main(void) {
  void *target = &&done;
  goto *target;
done:
  return 0;
}

// expect: 3:18: labels as values (computed 'goto')
