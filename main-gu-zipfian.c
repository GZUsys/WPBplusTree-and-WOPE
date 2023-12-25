#include "btree.h"
#include "zipfian.h"
#include "zipfian_util.h"
#include <cmath>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <vector>
#include <string.h>
#include <stdint.h>
#include <string>
#include <thread>
#include <atomic>
#include <immintrin.h>
extern "C"
{
    #include <atomic_ops.h>
}  

typedef uint64_t            setkey_t;
typedef void*               setval_t;

#define MAX_KEY         ((uint64_t)(0x7fffffffffffffffULL))
#define DEFAULT_DURATION                5000
#define DEFAULT_INITIAL                 100
#define DEFAULT_NB_THREADS              1
#define DEFAULT_RANGE                   0x7FFFFFFF
#define DEFAULT_SEED                    0
#define DEFAULT_UPDATE                  100
#define DEFAULT_ALTERNATE               0
#define DEFAULT_EFFECTIVE               0 
#define DEFAULT_UNBALANCED              0

#define XSTR(s)                         STR(s)
#define STR(s)                          #s

#define VAL_MIN                         INT_MIN
#define VAL_MAX                         INT_MAX
#define DETECT_LATENCY
//#define UNIFORM
int initial =     DEFAULT_INITIAL; 
unsigned int levelmax;
uint64_t records[50000000]={0};
uint64_t record[10][5000000]={0};
uint64_t latency, insert_nb[10] = {0},insert_nbs = 0;
__thread struct timespec T1[10], T2[10];
std::vector<uint64_t> buffer;
std::vector<uint64_t> sbuffer;
std::vector<long> slen;
std::vector<char> ops;
long sfencenum=0;
long clwbnum=0;
long alloer=0;
long Ialloer=0;
long splitnum=0;
void read_data_from_file(char* file)
{
    long count = 0;

    FILE* fp = fopen(file, "r");
    if (fp == NULL) {
        exit(-1);
    }
    buffer.clear();
    printf("reading\n");
    while (1) {
        unsigned long long key;
        count = fscanf(fp, "%lld\n", &key);
        if (count != 1) {
            break;
        }
        buffer.push_back(key);
    }
    fclose(fp);
    printf("file closed\n");
}


void scan_data_from_file(char* file)
{
    long count = 0;

    FILE* fp = fopen(file, "r");
    if (fp == NULL) {
        exit(-1);
    }
    buffer.clear();
    ops.clear();
    printf("reading\n");
    while (1) {
        char str[100];
	char * p;
        count = fscanf(fp, "%s\n",str);
        if (count != 1) {
            break;
        }
	p=strtok(str,","); 
        buffer.push_back(atoll(p));
	p=strtok(NULL,",");
        ops.push_back(p[0]);
    }
    fclose(fp);
    printf("file closed\n");
}

void sd_data_from_file(char* file)
{
    long count = 0;

    FILE* fp = fopen(file, "r");
    if (fp == NULL) {
        exit(-1);
    }
    buffer.clear();
    slen.clear();
    printf("reading\n");
    while (1) {
        char str[100];
        char * p;
        count = fscanf(fp, "%s\n",str);
        if (count != 1) {
            break;
        }
        p=strtok(str,",");
        buffer.push_back(atoll(p));
        p=strtok(NULL,",");
        slen.push_back(atol(p));
    }
    fclose(fp);
    printf("file closed\n");
}



int main(int argc, char **argv)
{
     
    char loading_file[100];
    sprintf(loading_file, "%s", "/root/HXY/ubtree/datafile/loadb.csv");
    read_data_from_file(loading_file);
    memset(record, 0, sizeof(record));
    btree *bt;
    bt = new btree();
    initial=buffer.size();
    struct timeval start_time, end_time;
    uint64_t     time_interval;
  int	worker_thread_num=1;
  int keys_per_thread=50000000;
         std::thread threads[128];
                for (int kt = 0; kt < 1; kt++) {
                    threads[kt] = std::thread([=]() {
                        int start = 0;
                        int end = 50000000;
                        for (int ii = start; ii < end; ii++) {
                            uint64_t kk=buffer[ii];
			    //printf("%lld\n",kk);
                            bt->insert(kk, (void*) kk);
                        }
                        });
                }
                for (int t = 0; t < 1; t++) threads[t].join();
printf("load is end\n");

    printf("clwb num  is   : %lld\n",             clwbnum);
    printf("sfence num is    : %lld\n",             sfencenum);
    printf("allo is    : %d\n",             alloer);
    printf("Ialloer num  is   : %lld\n",             Ialloer);

splitnum=0;
clwbnum=0;
sfencenum=0;
alloer=0;
Ialloer=0;
    bt->print();
    
            buffer.clear();
            sprintf(loading_file, "%s", "/root/HXY/ubtree/datafile/insert50m.csv");
            //scan_data_from_file(loading_file);
 	    read_data_from_file(loading_file);
 	    //sd_data_from_file(loading_file);
	    
	    gettimeofday(&start_time, NULL);
                for (int kt = 0; kt < worker_thread_num; kt++) {
                    threads[kt] = std::thread([=]() {                    
                        int start = keys_per_thread * kt;
                        int end = start+keys_per_thread;
                        for (int ii = start; ii < end; ii++) {
                        uint64_t kk = buffer[ii];
                        //char op = (char)ops[ii];
                        uint64_t endk=MAX_KEY;
                        long lend;
                      	char op;op='i';
		      // printf("%lld\n",ii);
		
                       //lend=slen[ii];
                        //if(lend > 0){op='s';}
			//else{op='i';}

			switch (op)
                        {
                        case 'r':
				//clock_gettime(CLOCK_MONOTONIC, &T1[kt]);
                                bt->search(kk); 
				//clock_gettime(CLOCK_MONOTONIC, &T2[kt]);
                                //latency = ((T2[kt].tv_sec - T1[kt].tv_sec) * 1000000000 + (T2[kt].tv_nsec - T1[kt].tv_nsec)) / 100;
                                //record[kt][latency] += 1;
                                //insert_nb[kt] += 1;
				break;
                        case 'i':
				//clock_gettime(CLOCK_MONOTONIC, &T1[kt]);
                                bt->insert(kk,(void*)kk);
				//clock_gettime(CLOCK_MONOTONIC, &T2[kt]);
                                //latency = ((T2[kt].tv_sec - T1[kt].tv_sec) * 1000000000 + (T2[kt].tv_nsec - T1[kt].tv_nsec)) / 100;
                                //record[kt][latency] += 1;
                                //insert_nb[kt] += 1;
				break;
                        case 'd':
				//clock_gettime(CLOCK_MONOTONIC, &T1[kt]);
                                bt->remove(kk); 
				//clock_gettime(CLOCK_MONOTONIC, &T2[kt]);
                                //latency = ((T2[kt].tv_sec - T1[kt].tv_sec) * 1000000000 + (T2[kt].tv_nsec - T1[kt].tv_nsec)) / 100;
                                //record[kt][latency] += 1;
                                //insert_nb[kt] += 1;
				break;
                        case 's':
				//clock_gettime(CLOCK_MONOTONIC, &T1[kt]);
                                bt->scan(kk,endk,lend);
				//clock_gettime(CLOCK_MONOTONIC, &T2[kt]);
                                //latency = ((T2[kt].tv_sec - T1[kt].tv_sec) * 1000000000 + (T2[kt].tv_nsec - T1[kt].tv_nsec)) / 100;
                                //record[kt][latency] += 1;
                                //insert_nb[kt] += 1;
                                break;
                        default :
                                printf("error\n");
                                break;
                        }

                        }
                        });
                }
                for (int t = 0; t < worker_thread_num; t++) threads[t].join();

    gettimeofday(&end_time, NULL);
   
    time_interval = 1000000 * (end_time.tv_sec - start_time.tv_sec) + end_time.tv_usec - start_time.tv_usec;
    printf("delete time_interval = %lu ns\n", time_interval * 1000);
    printf("average delete op = %lu ns\n",    time_interval * 1000 / initial);
    printf("Level max    : %d\n",             bt->level());
  bt->print();
 
    printf("clwb num  is   : %lld\n",             clwbnum);
    printf("sfence num is    : %lld\n",             sfencenum);
    //printf("Level max    : %d\n",             splitnum);
   // printf("clwb num  is   : %lld\n",             clwbnum);
    printf("Ialloer num is    : %lld\n",             Ialloer);
    printf("alloer is    : %d\n",             alloer);
    
  /*
    for(int ik=0;ik<50000000;ik++)
    {
	uint64_t kks = buffer[ik];
	uint64_t cnt = bt->search(kks);
	assert(cnt==kks);
    }
    */
    /*
        for(int ik=0;ik<10;ik++)
    {
        for(int jf=0;jf<5000000;jf++)
        {
           if(ik == 0 && record[ik][jf] != 0)
           {
             records[jf]=record[ik][jf];
           }
           if(ik > 0)
           {
              if(record[ik][jf] != 0 && records[jf]==0){records[jf]=record[ik][jf];}
              if(record[ik][jf] != 0 && records[jf]!=0){records[jf]=records[jf] + record[ik][jf];}
           }
        }
        insert_nbs=insert_nb[ik]+insert_nbs;
    }


        uint64_t cnt = 0;
        uint64_t nb_min = insert_nbs * 0.1;
        uint64_t nb_50 = insert_nbs / 2;
        uint64_t nb_90 = insert_nbs * 0.9;
        uint64_t nb_99 = insert_nbs * 0.99;
	uint64_t nb_999 = insert_nbs * 0.999;
	uint64_t nb_9999 = insert_nbs * 0.9999;
        bool flag_50 = false, flag_90 = false, flag_99 = false,flag_min=false,flag_999 = false,flag_9999 = false;
        double latency_50, latency_90, latency_99, latency_min,latency_999,latency_9999;
        for (int i=0; i < 50000000 && !(flag_min && flag_50 && flag_90 && flag_99 &&flag_999 && flag_9999); i++){
            cnt += records[i];
            if (!flag_min && cnt >= nb_min){
                latency_min = (double)i / 10.0;
                flag_min = true;
            }
            if (!flag_50 && cnt >= nb_50){
                latency_50 = (double)i / 10.0;
                flag_50 = true;
            }
            if (!flag_90 && cnt >= nb_90){
                latency_90 = (double)i / 10.0;
                flag_90 = true;
            }
            if (!flag_99 && cnt >= nb_99){
                latency_99 = (double)i / 10.0;
                flag_99 = true;
            }
	    if (!flag_999 && cnt >= nb_999){
                latency_999 = (double)i / 10.0;
                flag_999 = true;
            }
	    if (!flag_9999 && cnt >= nb_9999){
                latency_9999 = (double)i / 10.0;
                flag_9999 = true;
            }
        }
        printf("min latency is %.1lfus\nmedium latency is %.1lfus\n90%% latency is %.1lfus\n99%% latency is %.1lfus\n,99%% latency is %.1lfus\n,99%% latency is %.1lfus\n", latency_min,latency_50, latency_90, latency_99,latency_999,latency_9999);
	*/
    return 0;
}


