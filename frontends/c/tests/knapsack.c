/* Dynamic programming over arrays: 0/1 knapsack, longest common subsequence with
 * reconstruction, and edit distance; printed with printf. */
#include <stdio.h>

static int max(int a, int b) { return a > b ? a : b; }
static int min3(int a, int b, int c) { return a < b ? (a < c ? a : c) : (b < c ? b : c); }

static int knapsack(const int *w, const int *v, int n, int cap) {
  static int best[1001];
  for (int c = 0; c <= cap; c++) best[c] = 0;
  for (int i = 0; i < n; i++)
    for (int c = cap; c >= w[i]; c--) best[c] = max(best[c], best[c - w[i]] + v[i]);
  return best[cap];
}

static int lcs(const char *a, const char *b, char *out) {
  static int t[64][64];
  int n = 0, m = 0;
  while (a[n]) n++;
  while (b[m]) m++;
  for (int i = n; i >= 0; i--)
    for (int j = m; j >= 0; j--)
      t[i][j] = (i == n || j == m) ? 0 : a[i] == b[j] ? 1 + t[i + 1][j + 1] : max(t[i + 1][j], t[i][j + 1]);
  int i = 0, j = 0, k = 0;
  while (i < n && j < m) {
    if (a[i] == b[j]) { out[k++] = a[i]; i++; j++; }
    else if (t[i + 1][j] >= t[i][j + 1]) i++;
    else j++;
  }
  out[k] = 0;
  return t[0][0];
}

static int edit(const char *a, const char *b) {
  int prev[64], cur[64], n = 0, m = 0;
  while (a[n]) n++;
  while (b[m]) m++;
  for (int j = 0; j <= m; j++) prev[j] = j;
  for (int i = 1; i <= n; i++) {
    cur[0] = i;
    for (int j = 1; j <= m; j++)
      cur[j] = min3(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] != b[j - 1]));
    for (int j = 0; j <= m; j++) prev[j] = cur[j];
  }
  return prev[m];
}

int main(void) {
  int w[] = {12, 7, 11, 8, 9, 6, 15, 3, 4, 10}, v[] = {24, 13, 23, 15, 16, 11, 29, 5, 7, 19};
  printf("knapsack 26: %d\n", knapsack(w, v, 10, 26));
  printf("knapsack 50: %d\n", knapsack(w, v, 10, 50));
  char out[64];
  int n = lcs("AGGTABQRSTUVW", "GXTXAYBRTUW", out);
  printf("lcs %d \"%s\"\n", n, out);
  printf("edit kitten sitting: %d\n", edit("kitten", "sitting"));
  printf("edit intention execution: %d\n", edit("intention", "execution"));
  return 0;
}
