#define MYOBJECT_MYTAB_SIZE 5

typedef struct MyObject{
	int id;
	int myTab[MYOBJECT_MYTAB_SIZE];
}MyObject;

/*@	requires \valid(self);
	requires Inv2 : \forall int it_x; (0 <= it_x <= MYOBJECT_MYTAB_SIZE-1) ==> \let x=self->myTab[it_x];(x == 0) ;
	requires Inv1 : self->id == 0 ;
	assigns *self;
	ensures Inv2 : \forall int it_x; (0 <= it_x <= MYOBJECT_MYTAB_SIZE-1) ==> \let x=self->myTab[it_x];(x == 0) ;
	ensures Inv1 : self->id == 0 ;
*/
void test(MyObject* self){
	self->id = 0;
	for (int i=0; i<MYOBJECT_MYTAB_SIZE-1;i++){
		self->myTab[i] = 0;
	}
}
