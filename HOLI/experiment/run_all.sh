for file in programs/safe/equivalence/*.holi; do echo $file; krun --search --pattern "<k> fail </k> <trace> T </trace>" $file; done

for file in programs/safe/*.holi; do echo $file; krun --search --pattern "<k> fail </k> <trace> T </trace>" $file; done

for file in programs/unsafe/equivalence/*.holi; do echo $file; krun --search --pattern "<k> fail </k> <trace> T </trace>" $file; done

for file in programs/unsafe/*.holi; do echo $file; krun --search --pattern "<k> fail </k> <trace> T </trace>" $file; done

