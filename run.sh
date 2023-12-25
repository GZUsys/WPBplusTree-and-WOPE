#!/bin/bash

for skewness in 99 #0 90 99
do
for thread_num in 10 #1 4 8 12 16 20 24 28 32 36 
do

echo thread_num = ${thread_num} skewness = ${skewness}
./main-gu-zipfian -t ${thread_num} -d 5000 -i 100000 -u 5 -f 0  #> result/u5_0.${skewness}_${thread_num}.txt
rm /mnt/ext4/utree/pool
sleep 1
done
done

