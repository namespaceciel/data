#include <vector>
#include <array>
#include <string>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>


// int整型的二进制表示中 1 的个数

int bitCount(int i) {
	i = i - ((i >> 1) & 0x55555555);
	i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
	i = (i + (i >> 4)) & 0x0f0f0f0f;
	i = i + (i >> 8);
	i = i + (i >> 16);
	return i & 0x3f;
}


// 离散化

std::vector<int> arrayRankTransform(std::vector<int>& arr) {
	std::vector<int> temp = arr;
	std::sort(temp.begin(), temp.end());
	temp.erase(std::unique(temp.begin(), temp.end()), temp.end());
	for (int& i : arr) {
		i = std::upper_bound(temp.begin(), temp.end(), i) - temp.begin();
	}
	return arr;
}


// 取模快速幂

long long powMOD(long long x, int n, int mod) {
	long long res = 1;
	while (n) {
		if (n % 2 == 1) {
			res = res * x % mod;
		}
		x = x * x % mod;
		n /= 2;
	}
	return res;
}


// 约瑟夫环

int cir(int n, int k) {
	int p = 0;
	for (int i = 2; i <= n; i++) {
		p = (p + k) % i;
	}
	return p; //编号从0开始
}


// 1000以内的质数表

inline static std::unordered_set<int> prime =
	{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
	 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337,
	 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523,
	 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
	 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947,
	 953, 967, 971, 977, 983, 991, 997};


// 下一个全排列

void nextPermutation(std::vector<int>& nums) {//从右往左找到第一个比右一小的数，调换后，把后面排序
	for (int i = nums.size() - 1; i > -1; --i) {
		for (int j = nums.size() - 1; j > i; --j) {
			if (nums[i] < nums[j]) {
				std::swap(nums[i], nums[j]);
				std::sort(nums.begin() + i + 1, nums.end());
				return;
			}
		}
	}
	std::sort(nums.begin(), nums.end());//从最大跳到最小
}


// 1e9以内的斐波那契数

inline static std::unordered_set<int> fibonacciNumbers =
	{1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811, 514229,
	 832040, 1346269, 2178309, 3524578, 5702887, 9227465, 14930352, 24157817, 39088169, 63245986, 102334155, 165580141, 267914296, 433494437, 701408733};


// gcd

int gcd(int a, int b) {
	return b == 0 ? a : gcd(b, a % b);
}


// 不带删除移动撤销的基础并查集

struct DSU {
	std::vector<int> parents, eachSize;

	explicit DSU(int n) : eachSize(n, 1) {
		parents.reserve(n);
		for (int i = 0; i < n; ++i) {
			parents.push_back(i);
		}
	}

	int findParent(int index) {    //路径压缩
		return parents[index] == index ? index : parents[index] = findParent(parents[index]);
	}

	bool unionParents(int A, int B) {    //启发式合并
		int ARes = findParent(A);
		int BRes = findParent(B);
//		if (ARes == BRes) {
//			return false;	//已经是一个集合了
//		}
		if (eachSize[ARes] < eachSize[BRes]) {
			std::swap(ARes, BRes);
		}
		parents[BRes] = ARes;
		eachSize[ARes] += eachSize[BRes];
		return true;
	}
};


// 区间加减Lazy线段树

class SegmentTree_LazyRangeAdd {
private:
	std::vector<long long> tree, lazy;
	std::vector<int>* arr;
	int n, root, n4, end;

	void _maintain(int left, int right, int index) {
		int mid = left + (right - left) / 2;
		if (left != right && lazy[index]) {
			lazy[index * 2] += lazy[index];
			lazy[index * 2 + 1] += lazy[index];
			tree[index * 2] += lazy[index] * (mid - left + 1);
			tree[index * 2 + 1] += lazy[index] * (right - mid);
			lazy[index] = 0;
		}
	}

	long long _range_sum(int L, int R, int left, int right, int index) {
		if (L <= left && right <= R) {
			return tree[index];
		}
		int mid = left + (right - left) / 2;
		long long sum = 0;
		_maintain(left, right, index);
		if (L <= mid) {
			sum += _range_sum(L, R, left, mid, index * 2);
		}
		if (R > mid) {
			sum += _range_sum(L, R, mid + 1, right, index * 2 + 1);
		}
		return sum;
	}

	void _range_add(int L, int R, int val, int left, int right, int index) {
		if (L <= left && right <= R) {
			lazy[index] += val;
			tree[index] += (right - left + 1) * val;
			return;
		}
		int mid = left + (right - left) / 2;
		_maintain(left, right, index);
		if (L <= mid) {
			_range_add(L, R, val, left, mid, index * 2);
		}
		if (R > mid) {
			_range_add(L, R, val, mid + 1, right, index * 2 + 1);
		}
		tree[index] = tree[index * 2] + tree[index * 2 + 1];
	}

	void _build(int left, int right, int index) {
		if (left == right) {
			tree[index] = (*arr)[left];
			return;
		}
		int mid = left + (right - left) / 2;
		_build(left, mid, index * 2);
		_build(mid + 1, right, index * 2 + 1);
		tree[index] = tree[index * 2] + tree[index * 2 + 1];
	}

public:
	explicit SegmentTree_LazyRangeAdd(std::vector<int>& v) {
		n = v.size();
		n4 = n * 4;
		tree = std::vector<long long>(n4, 0);
		lazy = std::vector<long long>(n4, 0);
		arr = &v;
		end = n - 1;
		root = 1;
		_build(0, end, 1);
		arr = nullptr;
	}

	long long range_sum(int left, int right) {
		return _range_sum(left, right, 0, end, root);
	}

	void range_add(int left, int right, int val) {
		_range_add(left, right, val, 0, end, root);
	}
};


// 区间修改Lazy线段树

class SegmentTree_LazyRangeSet {
private:
	std::vector<long long> tree, lazy;
	std::vector<int>* arr;
	int n, root, n4, end;

	void _maintain(int left, int right, int index) {
		int mid = left + (right - left) / 2;
		if (left != right && lazy[index]) {
			lazy[index * 2] = lazy[index];
			lazy[index * 2 + 1] = lazy[index];
			tree[index * 2] = lazy[index] * (mid - left + 1);
			tree[index * 2 + 1] = lazy[index] * (right - mid);
			lazy[index] = 0;
		}
	}

	long long _range_sum(int L, int R, int left, int right, int index) {
		if (L <= left && right <= R) {
			return tree[index];
		}
		int mid = left + (right - left) / 2;
		long long sum = 0;
		_maintain(left, right, index);
		if (L <= mid) {
			sum += _range_sum(L, R, left, mid, index * 2);
		}
		if (R > mid) {
			sum += _range_sum(L, R, mid + 1, right, index * 2 + 1);
		}
		return sum;
	}

	void _range_set(int L, int R, int val, int left, int right, int index) {
		if (L <= left && right <= R) {
			lazy[index] = val;
			tree[index] = (right - left + 1) * val;
			return;
		}
		int mid = left + (right - left) / 2;
		_maintain(left, right, index);
		if (L <= mid) {
			_range_set(L, R, val, left, mid, index * 2);
		}
		if (R > mid) {
			_range_set(L, R, val, mid + 1, right, index * 2 + 1);
		}
		tree[index] = tree[index * 2] + tree[index * 2 + 1];
	}

	void _build(int left, int right, int index) {
		if (left == right) {
			tree[index] = (*arr)[left];
			return;
		}
		int mid = left + (right - left) / 2;
		_build(left, mid, index * 2);
		_build(mid + 1, right, index * 2 + 1);
		tree[index] = tree[index * 2] + tree[index * 2 + 1];
	}

public:
	explicit SegmentTree_LazyRangeSet(std::vector<int>& v) {
		n = v.size();
		n4 = n * 4;
		tree = std::vector<long long>(n4, 0);
		lazy = std::vector<long long>(n4, 0);
		arr = &v;
		end = n - 1;
		root = 1;
		_build(0, end, 1);
		arr = nullptr;
	}

	long long range_sum(int left, int right) {
		return _range_sum(left, right, 0, end, root);
	}

	void range_set(int left, int right, int val) {
		_range_set(left, right, val, 0, end, root);
	}
};