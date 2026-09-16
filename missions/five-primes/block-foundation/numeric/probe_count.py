import math
# RESOLVE THE COUNT.  Cor 3.5's statement as published (Child 1):
#   vinogradovMinSumOdd q A B alpha theta x y :=
#     sum_{n in Ioc floor x floor y, odd} min(A, B/|sin(pi alpha n + theta)|)
#       <= ( (floor((y-x)/(2q)) + 1) : N ) * (2A + (2/pi) B q log(4q))
# Block: (L, R] with L=2jq+q/2, R=L+2q.  Take x=L, y=R  => (y-x)/(2q) = 2q/(2q) = 1
#   => floor(1)+1 = 2.  So the count is 2, giving 4A + 2(2/pi)Bq log4q.
# But the numbers show 2A + (2/pi)Bq log4q suffices.  Why?
#   Because the odd n in (L,R] number only q (not 2q!), and Cor 3.5's count
#   floor((y-x)/(2q))+1 = 2 already over-counts: the TRUE number of q-blocks
#   in the odd range is ceil(q/q) = 1.
# => the sharp count for an odd block of width 2q is 1, not 2.  Cor 3.5 as stated
#    (with +1) is lossy by exactly this +1 for short ranges.
print("count comparisons for a block of width 2q (L=2jq+q/2):")
for q in [4,10,100]:
    L=2*q//1+q/2; R=L+2*q
    print(f"  q={q:4d}: (R-L)/(2q) = {2*q/(2*q):.4f}  => floor+1 = {math.floor(2*q/(2*q))+1}")
    print(f"          #odd d in (L,R] = q = {q}  ;  #q-blocks in m-space = ceil(q/q) = 1")
print()
print("=> The sharp form needed:   sum_{odd d in (L,R]} min(A, B/|sin|) <= 1*(2A + (2/pi)Bq log4q)")
print("   i.e. Cor 3.5 with count replaced by 1 for ranges of width exactly 2q.")
print("   This is provable from Lemma 3.4 directly (Tao's (3.7) block argument),")
print("   OR from Cor 3.5 by noting floor(2q/(2q))+1 = 2 but the sum is over the")
print("   SAME n-range as ONE q-block in m-space => count 1.")
