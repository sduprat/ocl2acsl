#define TYPE1_CSTARRAY_SIZE 5

typedef struct Type1 {
  int id;
  int* array;
  int size_array;
  int cstArray[TYPE1_CSTARRAY_SIZE];
} Type1;

/*@	requires \valid(obj);
	assigns \nothing;
	ensures id_post : \result == (*obj).id ;
*/
int id(Type1* obj){
  return (*obj).id;
}

/*@	requires \valid(obj);
	requires zeros_pre : \let x=0;\exists int it_y; (0 <= it_y <= (*obj).size_array-1) && \let y=(*obj).array[it_y];(y != x) ;
	assigns *obj;
	ensures zeros_post : (\forall int it_x; (0 <= it_x <= (*obj).size_array-1) ==> \let x=(*obj).array[it_x];(x == 0)) && (\forall int i; 0 <= i <= (*obj).size_array-1 ==> (*obj).array[i] != 1) && (\exists int i; 0 <= i <= (*obj).size_array-1 && (*obj).array[i] == 0) ;
	ensures zeros_post2 : \forall int it_x; (0 <= it_x <= TYPE1_CSTARRAY_SIZE-1) ==> \let x=(*obj).cstArray[it_x];(x == 0) ;
*/
void zeros(Type1* obj){
	int i;
	for (int i=0;i<(*obj).size_array;i++){
		(*obj).array[i]=0;
	}
}

/*@	requires \valid(obj);
	assigns *obj;
	ensures inc_post : \old((*obj).id) == (*obj).id - 1 && (\old((*obj).id) == 0?\old((*obj).id) == 1:\old((*obj).id) != 1) ;
*/
void incId(Type1* obj){
	(*obj).id++;
}

/*@	requires \valid(obj);
	requires \valid(a+(0..size_a-1)) && size_a>=0;
	assigns \nothing;
	ensures equal_post2 : size_a!=(*obj).size_array || (\exists int i; 0 <= i <= size_a-1 && a[i] != (*obj).array[i]) ==> !\result ;
	ensures equal_post1 : (*obj).size_array==size_a && (\forall int i; 0 <= i <= (*obj).size_array-1 ==>(*obj).array[i] == a[i]) ==> \result ;
*/
int equal(Type1* obj, int* a, int size_a){
	if (size_a!=(*obj).size_array) return 0;
	int res = 1;
	int i;
	for (int i=0;i<size_a;i++){
		if (a[i]!=(*obj).array[i]) res = 0;
	}
	return res;
}
