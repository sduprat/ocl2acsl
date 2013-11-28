#define DATATYPE2_CN_SIZE 5
#define DATATYPE2_AN_SIZE 9

typedef struct DataType1 {
  int id;
} DataType1;

typedef struct DataType2 {
  DataType1 c1;
  DataType1 cN[DATATYPE2_CN_SIZE];
  DataType1* c;
  DataType1* a1;
  DataType1* aN[DATATYPE2_AN_SIZE];
  DataType1** a;
  int size_c;
  int size_a;
} DataType2;

/*@	requires \valid(obj);
	assigns *obj;
	ensures test_post : ((*obj).c1).id == 0 && (\forall int it_x; (0 <= it_x <= DATATYPE2_CN_SIZE-1) ==> \let x=(*obj).cN[it_x];((x).id == 0)) && (\forall int it_x; (0 <= it_x <= (*obj).size_c-1) ==> \let x=(*obj).c[it_x];((x).id == 0)) && (*((*obj).a1)).id == 0 && (\forall int it_x; (0 <= it_x <= DATATYPE2_AN_SIZE-1) ==> \let x=*((*obj).aN[it_x]);((x).id == 0)) && (\forall int it_x; (0 <= it_x <= (*obj).size_a-1) ==> \let x=*((*obj).a[it_x]);((x).id == 0)) ;
*/
void test(DataType2* obj){
	((*obj).c1).id = 0;

	for (int i=0;i<DATATYPE2_CN_SIZE;i++){
		(*obj).cN[i].id=0;
	}

	for (int i=0;i<(*obj).size_c;i++){
		(*obj).c[i].id=0;
	}

	(*(*obj).a1).id = 0;

	for (int i=0;i<DATATYPE2_AN_SIZE;i++){
		(*(*obj).aN[i]).id=0;
	}

	for (int i=0;i<(*obj).size_a;i++){
		(*(*obj).a[i]).id=0;
	}
}
