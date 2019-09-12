// query.c ... query scan functions
// part of Multi-attribute Linear-hashed Files
// Manage creating and using Query objects
// Last modified by John Shepherd, July 2019

#include "defs.h"
#include "query.h"
#include "reln.h"
#include "tuple.h"
#include "hash.h"
#include <string.h>

// A suggestion ... you can change however you like

struct QueryRep {
	Reln    rel;       // need to remember Relation info
	Bits    known;     // the hash value from MAH
	Bits    unknown;   // the unknown bits from MAH
	PageID  curpage;   // current page in scan
	int     is_ovflow; // are we in the overflow pages?
	Offset  curtup;    // offset of current tuple within page
	
	//Solution
	char * q_str;
	Tuple q_tuple;
	PageID pid;
	PageID ovpid;
	char ** vals;
	char ** vals_tmp;
	int attr_num;
	int * known_attr;
	int known_bits[32];
	Bits * all_hash_values;
	Count d;
	Bits hash;			// query tuple hash val
	Count unknown_bits_num;
	Count sp;
	ChVecItem * cv;
	Bits hash_mask; // mask those bits where hash val fits in
	
	Count scaned_page_tuple_num;
	Count scaned_page_tuple_num_ovf;
	Bool is_new_page;
	Bool is_new_ovf_page;
	char * data_ptr;
	char * data_ptr_ovf;
};

// take a query string (e.g. "1234,?,abc,?")
// set up a QueryRep object for the scan

Query startQuery(Reln r, char *q)
{
	Query new = malloc(sizeof(struct QueryRep));
	assert(new != NULL);

	// Check if q is in valid form
	int valid_q = query_checker(r, q);
	if (!valid_q) return NULL;
	new->q_str = copyString(q);
	assert(new->q_str!=NULL);
	Count unknow_attr_num = 0;

	new->is_ovflow = 0;
	new->rel = r; 					// corresponding relation
	new->pid = 0;					// page id for tuple retrieval loop
	new->ovpid = 0;					// overflow page id for tuple retrieval loop
	new->attr_num = nattrs(r);		// attribuate number of relation
	new->d = depth(r);				// depth of relation r
	new->sp = splitp(r);
	new->cv = chvec(r);

	new->q_tuple = copyString(q); 	// a copy of query string, need to be free
	
	new->all_hash_values=NULL;
	new->all_hash_values = malloc(nattrs(r)*sizeof(Bits));
	assert(new->all_hash_values != NULL);

	new->known_attr = NULL;
	new->known_attr = malloc(nattrs(r)*sizeof(int));
	assert(new->known_attr != NULL);
	
	new->vals = NULL;				// list of query elements in string form
	new->vals = malloc(nattrs(r)*sizeof(char *));
	assert(new->vals != NULL);
	tupleVals(q, new->vals);		// parse tuple string to list of query elements
	
	new->vals_tmp = NULL;				// list of query elements in string form
	new->vals_tmp = malloc(nattrs(r)*sizeof(char *));
	assert(new->vals != NULL);
	//tupleVals(q, new->vals);		// parse tuple string to list of query elements

	for (int i = 0; i < new->attr_num; i++) {
		if (strcmp(new->vals[i],"?")==0){
			new->known_attr[i] = 0;
			new->all_hash_values[i] = 0;
			unknow_attr_num++;
		} else {
			new->known_attr[i] = 1;
			new->all_hash_values[i] = \
				hash_any((unsigned char *)(new->vals[i]), strlen(new->vals[i]));
		}
		// printf("%d %s\n", i, new->vals[i]);
	}

	new->hash = 0;
	for (int i = 0; i < 32; i++) {
		// printf("%d, %d\n", (new->cv[i].att), (new->cv[i].bit));
		new->hash += (((new->all_hash_values[new->cv[i].att] << (31-(new->cv[i].bit))) >> 31)) << i;
		if (new->known_attr[new->cv[i].att] == 1) {
			new->known_bits[i] = 1;
		}
		else {
			new->known_bits[i] = 0;
		}
	}

	Bits hash_mask = 0;
	for(int i = 31; i >=0; i--){
		// printf("%d", new->known_bits[i]);
		hash_mask += new->known_bits[i] << i;
	}
	// printf("\n");
	
	new->pid = getLower(new->hash,new->d);
	if (new->pid < new->sp)
		new->pid = getLower(new->hash,new->d+1);

	new->scaned_page_tuple_num = 0;
	new->is_new_page = TRUE;
	new->is_new_ovf_page = TRUE;
	new->data_ptr_ovf = NULL;
	new->data_ptr = NULL;
	// End solution
	return new;
}

Tuple getNextTuple(Query q)
{
	/////// Solution /////// 
	Reln rel = q->rel;
	Count d = depth(rel);
	Count sp = splitp(rel);
	FILE * df = dataFile(rel);
	FILE * ovf = ovflowFile(rel);
	Page p;
	Page ovp;
	Count page_tuple_num;
	Bool tuple_found = FALSE;
	Bool tuple_match = FALSE;
	char * res;
	//////////////////////////

	while (q->pid < (1 << d) + sp) 
	{
		tuple_found = FALSE;
		tuple_match = FALSE;

		Bits mask;
		if (q->pid < q->sp) 
		{
			mask = getLower(q->hash_mask,q->d+1);
		} else {
			mask = getLower(q->hash_mask,q->d);
		}
		if ((q->pid & mask) != mask) 
		{	
			//printf("not match!!!!!!");
			continue;
		}

		p = getPage(df, q->pid);

		// search in main data_page if currently not in ovf_page
		if (q->is_ovflow == 0) 
		{
			page_tuple_num = pageNTuples(p);
			if (q->is_new_page)
			{
				q->data_ptr = pageData(p);
				q->is_new_page = FALSE;
				q->is_new_ovf_page = TRUE;
				q->scaned_page_tuple_num = 0;
			}
			while (q->scaned_page_tuple_num < page_tuple_num) 
			{
				// parse tuple str to str list
				tupleVals(q->data_ptr, q->vals_tmp);
				tuple_match = TRUE;
				for (int j = 0; j < q->attr_num; j++) 
				{
					// pass unknown attr
					if (q->known_attr[j] != 1) continue;
					// known attr vals do not match
					if (strcmp(q->vals[j], q->vals_tmp[j]) != 0) {
						tuple_match = FALSE;
						break;
					}
				}
				if (tuple_match  == TRUE) {
					tuple_found = TRUE;
				} else {
					tuple_found = FALSE;
				}
				if (tuple_found == TRUE) {
					//printf("in data file pid = %d, %s = %s\n", q->pid, q->q_str, q->data_ptr);
					res = q->data_ptr;
					q->data_ptr += strlen(q->data_ptr)+1;
					q->scaned_page_tuple_num++;
					return res;
				}
				// point to next tuple string
				q->data_ptr += strlen(q->data_ptr)+1;
				q->scaned_page_tuple_num++;
			}
		}
		// if in ovf page or finished data page scanning
		// search in overflow data_page
		if (q->is_ovflow == 0) //if just goes from data page
		{
			q->ovpid = pageOvflow(p);// init q->ovpid
			if (q->ovpid != NO_PAGE)
				q->is_ovflow = 1; // set overflow flag to 1
		}
		while (q->ovpid != NO_PAGE) 
		{
			ovp = getPage(ovf, q->ovpid);
			page_tuple_num = pageNTuples(ovp);
			if (q->is_new_ovf_page) {
				q->data_ptr_ovf = pageData(ovp);
				q->is_new_ovf_page = FALSE;
				q->scaned_page_tuple_num_ovf = 0;
			}
			while(q->scaned_page_tuple_num_ovf < page_tuple_num) 
			{
				// parse tuple str to str list
				tupleVals(q->data_ptr_ovf, q->vals_tmp);
				tuple_match = TRUE;
				for (int j = 0; j < q->attr_num; j++) 
				{
					// pass unknown attr
					if (q->known_attr[j] != 1)
						continue;
					// known attr vals do not match
					else if (strcmp(q->vals[j], q->vals_tmp[j]) != 0) {
						tuple_match = FALSE;
						break;
					}
				}
				if (tuple_match  == TRUE) {
					tuple_found = TRUE;
				} else
					tuple_found = FALSE;

				if (tuple_found == TRUE) {
					//printf("in %d 's ovf file ovid = %d, %s = %s\n", q->pid,q->ovpid, q->q_str, q->data_ptr_ovf);
					res = q->data_ptr_ovf;
					q->data_ptr_ovf += strlen(q->data_ptr_ovf)+1;
					q->scaned_page_tuple_num_ovf++;
					return res;
				}
				// point to next tuple string
				q->data_ptr_ovf += strlen(q->data_ptr_ovf)+1; // +1 for '/0'
				q->scaned_page_tuple_num_ovf++;
			}
			// go to next ovf page
			q->ovpid = pageOvflow(ovp);
			q->is_new_ovf_page = TRUE;
		}
		// go to next bucket's data page
		q->pid++;
		//printf("from %d to %d \n", q->pid-1, q->pid);
		q->is_new_page = TRUE;
		q->is_ovflow = 0;
	}
	// can't find more tuple
	return NULL; 
}

// clean up a QueryRep object and associated data
void closeQuery(Query q)
{
	// TODO
	free(q->q_tuple);
	free(q->known_attr);
	free(q->all_hash_values);

	for (int i = 0; i < q->attr_num; i++) {
		free(q->vals[i]);
		free(q->vals_tmp[i]);
	}
	free (q->vals);
	free (q->vals_tmp);
	// free(q->canditate_pages);
	free(q->q_str);
	free(q);
}

// if invalid return 0
int query_checker(Reln r, char *q)
{
	// query string is to long
	if (strlen(q) >= MAXTUPLEN - 1) return 0;
	//char *q_cp = copyString(q);
	char *c; int nf = 1;
	for (c = q; *c != '\0'; c++)
		if (*c == ',') nf++;
	// check the number of attributes in query q
	if (nf != nattrs(r)) return 0;
	//free(q_cp);
	return 1;
}
