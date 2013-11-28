/*@	assigns \nothing;
	ensures add_post : \result == a + b && a == \result - b ;
*/
double add(double a, double b){
	return a+b;
}
/*@	assigns \nothing;
	ensures mult_post : \result == a * b && a == \result / b ;
*/
double mult(double a, double b){
	return a*b;
}
/*@	assigns \nothing;
	ensures max_post : \result == \max(a, b) && \result >= a && \result >= b ;
*/
double max(double a, double b){
	if (a>=b) return a;
	else return b;
}
/*@	requires \valid(a);
	assigns *a;
	ensures zero_post : \abs(*a) == 0 ;
*/
void zero(double* a){
	*a = 0;
}
