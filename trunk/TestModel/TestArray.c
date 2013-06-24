/*@	requires \valid(a+(0..size_a-1)) && size_a>=0 && \valid(b+(0..size_b-1)) && size_b>=0;
	requires equal_pre : (size_a!=size_b || (\exists int i; 0 <= i <= size_a-1 && a[i] != b[i])) && a[size_a-1] != 0 ;
	assigns \nothing;
	ensures equal_post2 : (\forall int i; 0 <= i <= size_b-1 ==> (\exists int j; 0<= j <= size_a-1 && a[j] == b[i])) ==> \result && (\forall int i; 0 <= i <= size_b-1 ==> (\forall int j; 0<= j <= size_a-1 ==> a[j] != b[i])) ==> !\result ;
	ensures equal_post : size_a == size_b && (\forall int i; (0 <= i <= size_a - 1) ==> a[i] == b[i]) ==> \result ;
*/
int equal(int* a, int size_a, int* b, int size_b) {
	int res = 1;
	int i;
	if (size_a != size_b)
		return 0;
	for (i = 0; i < size_a; i++) {
		if (a[i] != b[i])
			res = 0;
	}
	return res;
}

/*@	requires \valid(a+(0..size_a-1)) && size_a>=0;
	requires replace0_pre : size_a !=0 && !(size_a == 0) ;
	requires replace0_pre2 : \exists int it_x, int it_y; (0 <= it_x <= size_a-1 && 0 <= it_y <= size_a-1) && \let y=a[it_y];(\let x=a[it_x];(x != 0 && y != 0)) ;
	assigns a[0..size_a-1];
	ensures replace_post : size_a != 0 ;
	ensures replace_post2 : \exists int i; (0<=i<=size_a-1 && \let x=a[i];(x == 0) && (\forall int j; (0<=j<=size_a-1 && j!=i) ==> !(\let x=a[j];(x == 0)))) ;
	ensures replace0_post : a[0] == o && (\exists int i; 0 <= i <= size_a-1 && a[i] == o) ;
*/
void replace0(int* a, int o, int size_a){
	a[0]=o;
}

/*@	requires \valid(a+(0..size_a-1)) && size_a>=0;
	assigns a[0..size_a-1];
	ensures zeros_post : (\forall int it_x; (0 <= it_x <= size_a-1) ==> \let x=a[it_x];(x == 0)) && (\forall int i; 0 <= i <= size_a-1 ==> a[i] != 1) ;
*/
void zeros(int* a, int size_a){
	int i;
	for (int i=0;i<size_a;i++){
		a[i]=0;
	}
}
