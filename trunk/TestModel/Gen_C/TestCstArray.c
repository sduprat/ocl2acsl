#define EQUAL_B_SIZE 5
#define EQUAL_A_SIZE 5
#define ZEROS_A_SIZE 7

/*@	requires \valid(a+(0.. EQUAL_A_SIZE -1)) && EQUAL_A_SIZE >=0 && \valid(b+(0.. EQUAL_B_SIZE -1)) && EQUAL_B_SIZE >=0;
	assigns \nothing;
	ensures equal_post : \result ==> (\exists int i; 0 <= i <= EQUAL_A_SIZE-1 && a[i] == b[0]) ;
*/
int equal(int a[EQUAL_A_SIZE], int b[EQUAL_B_SIZE]) {
	int res = 1;
	int i;
	for (i = 0; i < EQUAL_A_SIZE; i++) {
		if (a[i] != b[i])
			res = 0;
	}
	return res;
}

/*@	requires \valid(a+(0.. ZEROS_A_SIZE -1)) && ZEROS_A_SIZE >=0;
	assigns a[0.. ZEROS_A_SIZE -1];
	ensures zeros_post : \forall int it_x; (0 <= it_x <= ZEROS_A_SIZE-1) ==> \let x=a[it_x];(x == 0) ;
*/
void zeros(int a[ZEROS_A_SIZE]){
	int i;
	for (int i=0;i<ZEROS_A_SIZE;i++){
		a[i]=0;
	}
}
