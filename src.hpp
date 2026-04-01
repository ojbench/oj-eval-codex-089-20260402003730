// Buddy Allocator implementation for Problem 089
// Avoids STL containers as per problem note.

namespace sjtu {

class BuddyAllocator {
public:
  BuddyAllocator(int ram_size, int min_block_size)
      : ram_size_(ram_size), min_block_size_(min_block_size) {
    // Compute number of minimal blocks and levels
    int n = ram_size_ / min_block_size_;
    L_ = 0;
    while ((1 << L_) < n) ++L_;

    // Allocate per-order arrays
    count_ = new int[L_ + 1];
    is_free_ = new unsigned char*[L_ + 1];
    max_free_ = new int*[L_ + 1];

    for (int o = 0; o <= L_; ++o) {
      int cnt = 1 << (L_ - o);
      count_[o] = cnt;
      is_free_[o] = new unsigned char[cnt];
      max_free_[o] = new int[cnt];
      for (int i = 0; i < cnt; ++i) {
        is_free_[o][i] = 0;
        max_free_[o][i] = -1;
      }
    }
    // Initially, the whole memory (order L_, index 0) is free.
    is_free_[L_][0] = 1;
    max_free_[L_][0] = L_;
  }

  ~BuddyAllocator() {
    if (is_free_) {
      for (int o = 0; o <= L_; ++o) {
        delete[] is_free_[o];
      }
      delete[] is_free_;
    }
    if (max_free_) {
      for (int o = 0; o <= L_; ++o) {
        delete[] max_free_[o];
      }
      delete[] max_free_;
    }
    delete[] count_;
  }

  int malloc(int size) {
    int t = order_from_size(size);
    if (t < 0) return -1;
    if (max_free_[L_][0] < t) return -1;

    int h = L_;
    int i = 0;
    int addr = 0;
    while (true) {
      if (is_free_[h][i]) {
        if (h == t) {
          // allocate here
          is_free_[h][i] = 0;
          // After allocation, update upwards
          update_upwards(h, i);
          return addr;
        } else {
          // split this block: mark not free and create two free children
          is_free_[h][i] = 0;
          int left_child = i << 1;
          int right_child = left_child | 1;
          is_free_[h - 1][left_child] = 1;
          is_free_[h - 1][right_child] = 1;
          max_free_[h - 1][left_child] = h - 1;
          max_free_[h - 1][right_child] = h - 1;
          // Descend to left child for minimal address
          h = h - 1;
          i = left_child;
          // addr unchanged (left half)
          continue;
        }
      } else {
        if (h == t) {
          return -1; // cannot allocate here
        }
        int left_child = i << 1;
        int right_child = left_child | 1;
        // Prefer left subtree if it can provide order t
        if (max_free_[h - 1][left_child] >= t) {
          h = h - 1;
          i = left_child;
          // addr unchanged
          continue;
        } else if (max_free_[h - 1][right_child] >= t) {
          // go right
          int half = block_size_from_order(h) >> 1;
          addr += half;
          h = h - 1;
          i = right_child;
          continue;
        } else {
          return -1;
        }
      }
    }
  }

  int malloc_at(int addr, int size) {
    int t = order_from_size(size);
    if (t < 0) return -1;
    if (addr < 0 || addr >= ram_size_) return -1;
    int s_t = block_size_from_order(t);
    if (addr % s_t != 0) return -1;
    if (max_free_[L_][0] < t) {
      return -1;
    }

    int h = L_;
    int i = 0;
    int cur_start = 0;
    while (true) {
      if (is_free_[h][i]) {
        if (h == t) {
          // allocate here
          is_free_[h][i] = 0;
          update_upwards(h, i);
          return addr;
        } else {
          // split and proceed towards the target address
          is_free_[h][i] = 0;
          int half = block_size_from_order(h) >> 1;
          int left_child = i << 1;
          int right_child = left_child | 1;
          // both children become free after split
          is_free_[h - 1][left_child] = 1;
          is_free_[h - 1][right_child] = 1;
          max_free_[h - 1][left_child] = h - 1;
          max_free_[h - 1][right_child] = h - 1;
          if (addr < cur_start + half) {
            // go left
            h = h - 1;
            i = left_child;
            // cur_start unchanged
          } else {
            // go right
            h = h - 1;
            i = right_child;
            cur_start += half;
          }
        }
      } else {
        if (h == t) {
          return -1;
        }
        int half = block_size_from_order(h) >> 1;
        int left_child = i << 1;
        int right_child = left_child | 1;
        if (addr < cur_start + half) {
          if (max_free_[h - 1][left_child] >= t) {
            h = h - 1;
            i = left_child;
            // cur_start unchanged
          } else {
            return -1;
          }
        } else {
          if (max_free_[h - 1][right_child] >= t) {
            h = h - 1;
            i = right_child;
            cur_start += half;
          } else {
            return -1;
          }
        }
      }
    }
  }

  void free_at(int addr, int size) {
    int t = order_from_size(size);
    if (t < 0) return;
    int s_t = block_size_from_order(t);
    if (addr < 0 || addr >= ram_size_) return;
    if (addr % s_t != 0) return;

    int idx = addr / s_t;
    int h = t;
    int i = idx;

    // free this block
    is_free_[h][i] = 1;
    max_free_[h][i] = h;

    // Try to merge upwards while buddy is free
    while (h < L_) {
      int buddy = i ^ 1;
      if (is_free_[h][buddy]) {
        // Merge: remove both children and mark parent free
        is_free_[h][buddy] = 0;
        max_free_[h][buddy] = -1;
        is_free_[h][i] = 0;
        max_free_[h][i] = -1;
        int parent_i = i >> 1;
        h = h + 1;
        i = parent_i;
        is_free_[h][i] = 1;
        max_free_[h][i] = h;
        // continue trying to merge further
      } else {
        break;
      }
    }
    // Update upwards to root to refresh aggregates
    update_upwards(h, i);
  }

private:
  int ram_size_;
  int min_block_size_;
  int L_;
  int *count_;
  unsigned char **is_free_;
  int **max_free_;

  inline int block_size_from_order(int o) const { return min_block_size_ << o; }

  int order_from_size(int size) const {
    // Find o such that min_block_size_ << o == size
    if (size < min_block_size_) return -1;
    int o = 0;
    int cur = min_block_size_;
    while (cur < size && o <= L_) {
      cur <<= 1;
      ++o;
    }
    if (cur == size && o <= L_) return o;
    return -1;
  }

  void update_upwards(int h, int i) {
    while (true) {
      int v = is_free_[h][i] ? h : -1;
      if (h > 0) {
        int left_child = i << 1;
        int right_child = left_child | 1;
        int ml = max_free_[h - 1][left_child];
        int mr = max_free_[h - 1][right_child];
        if (ml > v) v = ml;
        if (mr > v) v = mr;
      }
      max_free_[h][i] = v;
      if (h == L_) break;
      i >>= 1;
      ++h;
    }
  }
};

} // namespace sjtu
