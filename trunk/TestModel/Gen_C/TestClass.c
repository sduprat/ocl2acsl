#define CLASS1_PROP1_SIZE 5
#define CLASS2_CLASS1_SIZE 9

typedef struct Class1 {
	int prop1[CLASS1_PROP1_SIZE];
} Class1;

typedef struct Class2 {
	Class1 class1[CLASS2_CLASS1_SIZE];
}Class2;

/*@	requires \valid(self);
	assigns *self;
	ensures test_post : \forall int it_x; (0 <= it_x <= CLASS1_PROP1_SIZE-1) ==> \let x=(*self).prop1[it_x];(x == 0) ;
*/

void test(Class1* self){
	for(int i=0;i<CLASS1_PROP1_SIZE;i++){
		self->prop1[i]=0;
	}
}

/*@	requires \valid(self);
	assigns *self;
	ensures test2_post : \forall int it_c; (0 <= it_c <= CLASS2_CLASS1_SIZE-1) ==> \let c=(*self).class1[it_c];(\exists int i; 0 <= i <= CLASS1_PROP1_SIZE-1 && (c).prop1[i] == 0) ;
*/
void test2(Class2* self){
	for (int i=0;i<CLASS2_CLASS1_SIZE;i++){
		self->class1[i].prop1[0]=0;
	}
}
