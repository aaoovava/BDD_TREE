#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>

// -------------------- Data Structures --------------------
typedef struct BDDNode
{
    char var_name;
    int var_index;
    struct BDDNode *parent;
    struct BDDNode *high;
    struct BDDNode *low;
    int id;
    bool is_terminal;
    char value;
} BDDNode;

typedef struct
{
    BDDNode **nodes;
    int capacity;
    int size;
} NodeDictionary;

typedef struct
{
    BDDNode *root;
    char *var_order;
    int *var_priority;
    int var_count;
    int node_count;
    NodeDictionary unique;
} BDD;

// Structure to represent a variable with negation
typedef struct
{
    char name;
    bool negated;
} Variable;

// DNF term structure
typedef struct
{
    Variable *vars; // Array of variables with negation
    int length;
} DNFTerm;

// Context for sorting
typedef struct
{
    const int *var_priority;
} SortContext;

// -------------------- Functions --------------------

void init_var_priority(BDD *bdd)
{
    bdd->var_priority = (int *)malloc(26 * sizeof(int));
    for (int i = 0; i < 26; i++)
        bdd->var_priority[i] = -1;

    for (int i = 0; i < bdd->var_count; i++)
    {
        bdd->var_priority[toupper(bdd->var_order[i]) - 'A'] = bdd->var_count - i - 1;
    }
}

int compare_vars(void *context, const void *a, const void *b)
{
    SortContext *ctx = (SortContext *)context;
    const Variable *va = (const Variable *)a;
    const Variable *vb = (const Variable *)b;

    int prio_a = ctx->var_priority[toupper(va->name) - 'A'];
    int prio_b = ctx->var_priority[toupper(vb->name) - 'A'];

    // First sort by priority, then by negation (non-negated first)
    if (prio_a != prio_b)
        return prio_b - prio_a;
    return va->negated - vb->negated;
}

DNFTerm *normalize_dnf(const char *dnf, const char *var_order, int *term_count)
{
    BDD temp_bdd;
    temp_bdd.var_order = strdup(var_order);
    temp_bdd.var_count = strlen(var_order);
    init_var_priority(&temp_bdd);

    // Initial term count estimate
    char *copy = strdup(dnf);
    int estimated_terms = 1;
    for (char *p = copy; *p; p++)
        if (*p == '+')
            estimated_terms++;

    DNFTerm *terms = malloc(estimated_terms * sizeof(DNFTerm));
    SortContext ctx = {.var_priority = temp_bdd.var_priority};

    int valid_terms = 0;
    char *term_str = strtok(copy, "+");

    while (term_str != NULL)
    {
        // Parse variables with negations
        Variable vars[26];
        int pos = 0;
        bool in_negation = false;

        for (char *p = term_str; *p; p++)
        {
            if (*p == ' ')
                continue;

            if (*p == '!')
            {
                in_negation = true;
                continue;
            }

            if (isalpha(*p))
            {
                vars[pos].name = toupper(*p);
                vars[pos].negated = in_negation;
                pos++;
                in_negation = false;
            }
        }

        // Check for contradiction and remove duplicates
        bool contradiction = false;
        for (int j = 0; j < pos; j++)
        {
            for (int k = j + 1; k < pos; k++)
            {
                if (vars[j].name == vars[k].name)
                {
                    if (vars[j].negated != vars[k].negated)
                    {
                        contradiction = true;
                        break;
                    }
                    else
                    {
                        // Same polarity, remove duplicate
                        for (int l = k; l < pos - 1; l++)
                        {
                            vars[l] = vars[l + 1];
                        }
                        pos--;
                        k--;
                    }
                }
            }
            if (contradiction)
                break;
        }

        if (!contradiction)
        {
            qsort_r(vars, pos, sizeof(Variable), &ctx, compare_vars);
            terms[valid_terms].vars = malloc(pos * sizeof(Variable));
            memcpy(terms[valid_terms].vars, vars, pos * sizeof(Variable));
            terms[valid_terms].length = pos;
            valid_terms++;
        }

        term_str = strtok(NULL, "+");
    }

    free(copy);
    free(temp_bdd.var_order);
    free(temp_bdd.var_priority);

    *term_count = valid_terms;
    return terms;
}

void print_term(const DNFTerm *term)
{
    for (int i = 0; i < term->length; i++)
    {
        if (term->vars[i].negated)
            printf("!");
        printf("%c", term->vars[i].name);
    }
}

// -------------------- Main --------------------
int main()
{
    const char *dnf = "!AA + !BB + BC!B + C!A";
    const char *order = "ABC";

    int term_count;
    DNFTerm *terms = normalize_dnf(dnf, order, &term_count);

    printf("Original DNF: %s\n", dnf);
    printf("Variable order: %s\n", order);
    printf("Normalized terms:\n");

    for (int i = 0; i < term_count; i++)
    {
        printf("Term %d: ", i + 1);
        print_term(&terms[i]);
        printf("\n");
        free(terms[i].vars);
    }

    free(terms);
    return 0;
}