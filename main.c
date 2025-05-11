#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <time.h>

#define INT_MAX 2147483647

// -------------------- Data Structures --------------------
typedef struct BDDNode
{
    char var_name;
    int var_index;
    struct BDDNode *high;
    struct BDDNode *low;
    int id;
    bool is_terminal;
    char value;
    bool visited;
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

// -------------------- BDD Creation --------------------
BDDNode* create_terminal_node(BDD *bdd, char value) {
    for (int i = 0; i < bdd->unique.size; i++) {
        BDDNode *node = bdd->unique.nodes[i];
        if (node->is_terminal && node->value == value) {
            return node;
        }
    }

    BDDNode *node = malloc(sizeof(BDDNode));
    node->is_terminal = true;
    node->value = value;
    node->high = node->low = NULL;
    node->id = bdd->node_count++;  // Increment count here
    
    // Add to unique table
    if (bdd->unique.size >= bdd->unique.capacity) {
        bdd->unique.capacity *= 2;
        bdd->unique.nodes = realloc(bdd->unique.nodes, 
                                  bdd->unique.capacity * sizeof(BDDNode*));
    }
    bdd->unique.nodes[bdd->unique.size++] = node;
    
    return node;
}

void mark_reachable(BDDNode *node) {
    if (!node || node->visited) return;
    
    node->visited = true;
    
    if (!node->is_terminal) {
        mark_reachable(node->high);
        mark_reachable(node->low);
    }
}

void update_node_count(BDD *bdd) {
    // Reset visited flags
    for (int i = 0; i < bdd->unique.size; i++) {
        bdd->unique.nodes[i]->visited = false;
    }
    
    // Mark reachable nodes from root
    mark_reachable(bdd->root);
    
    // Count marked nodes
    int count = 0;
    for (int i = 0; i < bdd->unique.size; i++) {
        if (bdd->unique.nodes[i]->visited) {
            count++;
        }
    }
    
    bdd->node_count = count;
}

BDDNode* find_or_create_node(BDD *bdd, char var_name, int var_index, BDDNode *high, BDDNode *low) {
    // Eliminate redundant nodes (1st reduction)
    if (high == low) {
        return high;
    }

    // Check for existing isomorphic nodes (2nd reduction)
    for (int i = 0; i < bdd->unique.size; i++) {
        BDDNode *node = bdd->unique.nodes[i];
        if (!node->is_terminal &&
            node->var_name == var_name &&
            node->var_index == var_index &&
            node->high == high &&
            node->low == low) {
            return node;
        }
    }

    // Create new node
    BDDNode *node = malloc(sizeof(BDDNode));
    node->var_name = var_name;
    node->var_index = var_index;
    node->high = high;
    node->low = low;
    node->is_terminal = false;
    node->id = bdd->node_count++;
    
    // Add to unique table
    if (bdd->unique.size >= bdd->unique.capacity) {
        bdd->unique.capacity *= 2;
        bdd->unique.nodes = realloc(bdd->unique.nodes, 
                                  bdd->unique.capacity * sizeof(BDDNode*));
    }
    bdd->unique.nodes[bdd->unique.size++] = node;
    
    return node;
}

BDDNode* build_term_bdd(BDD *bdd, DNFTerm *term, int var_index) {
    if (var_index >= bdd->var_count) {
        // All variables processed - this term is satisfied
        return create_terminal_node(bdd, '1');
    }

    char current_var = bdd->var_order[var_index];
    bool exists = false;
    bool negated = false;

    // Check if variable exists in term
    for (int i = 0; i < term->length; i++) {
        if (term->vars[i].name == current_var) {
            exists = true;
            negated = term->vars[i].negated;
            break;
        }
    }

    BDDNode *high, *low;
    if (exists) {
        if (negated) {
            high = create_terminal_node(bdd, '0');  // If negated var is 1, term fails
            low = build_term_bdd(bdd, term, var_index + 1);  // If 0, continue
        } else {
            high = build_term_bdd(bdd, term, var_index + 1);  // If var is 1, continue
            low = create_terminal_node(bdd, '0');  // If 0, term fails
        }
    } else {
        // Variable not in term - continue with both branches
        BDDNode *child = build_term_bdd(bdd, term, var_index + 1);
        high = low = child;
    }

    return find_or_create_node(bdd, current_var, var_index, high, low);
}

BDDNode* bdd_or(BDD *bdd, BDDNode *f, BDDNode *g) {
    // Terminal cases
    if (f->is_terminal) return f->value == '1' ? f : g;
    if (g->is_terminal) return g->value == '1' ? g : f;

    // Same variable - merge branches
    if (f->var_index == g->var_index) {
        BDDNode *high = bdd_or(bdd, f->high, g->high);
        BDDNode *low = bdd_or(bdd, f->low, g->low);
        return find_or_create_node(bdd, f->var_name, f->var_index, high, low);
    }

    // Different variables - f comes first in order
    if (f->var_index < g->var_index) {
        BDDNode *high = bdd_or(bdd, f->high, g);
        BDDNode *low = bdd_or(bdd, f->low, g);
        return find_or_create_node(bdd, f->var_name, f->var_index, high, low);
    }
    
    // g comes first in order
    BDDNode *high = bdd_or(bdd, f, g->high);
    BDDNode *low = bdd_or(bdd, f, g->low);
    return find_or_create_node(bdd, g->var_name, g->var_index, high, low);
}

// In BDD_use(), add input validation:
char BDD_use(BDD *bdd, const char *inputs) {
    if (!bdd || !inputs) return -1;
    
    BDDNode *current = bdd->root;
    while (!current->is_terminal) {
        char var = current->var_name;
        int input_index = toupper(var) - 'A';
        
        if (input_index < 0 || input_index >= 26) {
            return -1;
        }
        
        if (inputs[input_index] != '0' && inputs[input_index] != '1') {
            return -1;
        }
        
        current = (inputs[input_index] == '1') ? current->high : current->low;
    }
    
    return current->value;
}

BDD* BDD_create(const char *dnf, const char *var_order) {
    int term_count;
    DNFTerm *terms = normalize_dnf(dnf, var_order, &term_count);

    BDD *bdd = malloc(sizeof(BDD));
    bdd->var_order = strdup(var_order);
    bdd->var_count = strlen(var_order);
    
    // Initialize counts FIRST
    bdd->node_count = 0;
    bdd->unique.size = 0;
    bdd->unique.capacity = 10;
    bdd->unique.nodes = malloc(10 * sizeof(BDDNode*));
    
    // Create terminals first
    BDDNode *zero = create_terminal_node(bdd, '0');
    BDDNode *one = create_terminal_node(bdd, '1');
    
    BDDNode *result = zero;

    for (int i = 0; i < term_count; i++) {
        if (terms[i].length == 0) continue;
        BDDNode *term_bdd = build_term_bdd(bdd, &terms[i], 0);
        result = bdd_or(bdd, result, term_bdd);
    }

    bdd->root = result;

    for (int i = 0; i < term_count; i++) free(terms[i].vars);
    free(terms);
    return bdd;
}

// Helper function to generate a random permutation of variables(Fisher-Yates)
void shuffle_order(char *order, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        char temp = order[i];
        order[i] = order[j];
        order[j] = temp;
    }
}

// Helper function to count unique variables in DNF
int count_unique_vars(const char *dnf) {
    bool vars[26] = {false};
    for (const char *p = dnf; *p; p++) {
        if (isalpha(*p)) {
            vars[toupper(*p) - 'A'] = true;
        }
    }
    int count = 0;
    for (int i = 0; i < 26; i++) {
        if (vars[i]) count++;
    }
    return count;
}

BDD* BDD_create_with_best_order(const char *dnf) {
    srand(time(NULL)); // Seed random number generator
    
    int num_vars = count_unique_vars(dnf);
    if (num_vars == 0) return NULL;
    
    // Create initial order (alphabetical)
    char base_order[26];
    int pos = 0;
    for (int i = 0; i < 26; i++) {
        if (strchr(dnf, 'A' + i) || strchr(dnf, 'a' + i)) {
            base_order[pos++] = 'A' + i;
        }
    }
    base_order[pos] = '\0';
    
    BDD *best_bdd = NULL;
    int best_size = INT_MAX;
    
    // Try at least N different orders (where N is number of variables)
    for (int i = 0; i < num_vars * 2; i++) {
        char current_order[27];
        strcpy(current_order, base_order);
        
        if (i > 0) { // After first try, shuffle the order
            shuffle_order(current_order, num_vars);
        }
        
        BDD *temp_bdd = BDD_create(dnf, current_order);
        update_node_count(temp_bdd); // Ensure accurate node count
        
        if (!best_bdd || temp_bdd->node_count < best_size) {
            if (best_bdd) {
                // Free previous best BDD
                for (int j = 0; j < best_bdd->unique.size; j++) 
                    free(best_bdd->unique.nodes[j]);
                free(best_bdd->unique.nodes);
                free(best_bdd->var_order);
                free(best_bdd);
            }
            best_bdd = temp_bdd;
            best_size = temp_bdd->node_count;
        } else {
            // Free the temporary BDD
            for (int j = 0; j < temp_bdd->unique.size; j++) 
                free(temp_bdd->unique.nodes[j]);
            free(temp_bdd->unique.nodes);
            free(temp_bdd->var_order);
            free(temp_bdd);
        }
    }
    
    return best_bdd;
}

// Function to generate a random DNF expression
char* generate_random_dnf(int var_count, int term_count) {
    char* dnf = malloc(1000 * sizeof(char));
    dnf[0] = '\0';

    // 1. Гарантируем использование всех переменных
    int required_terms = (term_count < var_count) ? var_count : term_count;
    char* vars = malloc(var_count * sizeof(char));
    
    // Создаем массив переменных и перемешиваем его
    for (int i = 0; i < var_count; i++) {
        vars[i] = 'A' + i;
    }
    for (int i = var_count-1; i > 0; i--) { // Fisher-Yates shuffle
        int j = rand() % (i+1);
        char temp = vars[i];
        vars[i] = vars[j];
        vars[j] = temp;
    }

    // 2. Распределяем обязательные переменные
    int vars_used = 0;
    for (int t = 0; t < required_terms; t++) {
        // Добавляем минимум одну новую переменную в каждый из первых var_count термов
        if (t < var_count && vars_used < var_count) {
            // Добавляем обязательную переменную
            if (rand() % 2) strcat(dnf, "!");
            char var_str[2] = {vars[vars_used++], '\0'};
            strcat(dnf, var_str);
            
            // Добавляем дополнительные переменные в терм
            int extra_vars = rand() % (var_count - vars_used + 1);
            for (int e = 0; e < extra_vars; e++) {
                strcat(dnf, (rand() % 2) ? "!" : "");
                char extra_str[2] = {vars[rand() % var_count], '\0'};
                strcat(dnf, extra_str);
            }
        }
        else {
            // Генерируем полностью случайный терм
            int term_length = 1 + rand() % var_count;
            bool used[26] = {false};
            
            for (int v = 0; v < term_length; v++) {
                int var_idx;
                do {
                    var_idx = rand() % var_count;
                } while (used[var_idx]);
                used[var_idx] = true;
                
                strcat(dnf, (rand() % 2) ? "!" : "");
                char var_str[2] = {vars[var_idx], '\0'};
                strcat(dnf, var_str);
            }
        }
        
        if (t < required_terms - 1) strcat(dnf, "+");
    }

    free(vars);
    return dnf;
}

// Function to evaluate a DNF expression directly
char evaluate_dnf(const char* dnf, const char* inputs) {
    // Make a copy we can modify
    char* expr = strdup(dnf);
    char* term = strtok(expr, "+");
    
    while (term != NULL) {
        bool term_true = true;
        char* p = term;
        
        while (*p) {
            // Skip whitespace
            if (*p == ' ') {
                p++;
                continue;
            }
            
            bool negated = false;
            if (*p == '!') {
                negated = true;
                p++;
                // Skip whitespace after negation
                while (*p == ' ') p++;
            }
            
            if (isalpha(*p)) {
                char var = toupper(*p);
                int var_idx = var - 'A';
                
                // Default to false if variable not in inputs
                bool var_value = false;
                
                // Check if variable exists in inputs
                if (var_idx >= 0 && var_idx < strlen(inputs)) {
                    var_value = (inputs[var_idx] == '1');
                }
                
                if (negated) {
                    var_value = !var_value;
                }
                
                if (!var_value) {
                    term_true = false;
                    break;
                }
            }
            
            p++;
        }
        
        if (term_true) {
            free(expr);
            return '1';
        }
        
        term = strtok(NULL, "+");
    }
    
    free(expr);
    return '0';
}

// Function to generate all possible input combinations
void test_all_combinations(BDD* bdd, const char* dnf, int var_count) {
    printf("Testing all combinations for DNF: %s\n", dnf);
    
    char* inputs = malloc((var_count + 1) * sizeof(char));
    inputs[var_count] = '\0';
    
    int total_tests = 1 << var_count;
    int passed = 0;
    
    // Bitmask enumeration
    for (int i = 0; i < total_tests; i++) {
        // Generate binary string
        for (int j = 0; j < var_count; j++) {
            inputs[j] = (i & (1 << (var_count - j - 1))) ? '1' : '0';
        }
        
        char expected = evaluate_dnf(dnf, inputs);
        char actual = BDD_use(bdd, inputs);
        
        if (expected != actual) {
            printf("Test failed for inputs %s: expected %c, got %c\n", 
                  inputs, expected, actual);
        } else {
            passed++;
        }
    }
    
    printf("Passed %d/%d tests (%.2f%%)\n\n", passed, total_tests, 
          (float)passed/total_tests*100);
    free(inputs);
}

// Function to test BDD creation and measure reduction
void test_bdd_creation(const char* dnf, const char* order) {
    printf("Testing BDD creation for DNF: %s\n", dnf);
    printf("Using order: %s\n", order);
    
    clock_t start = clock();
    BDD* bdd = BDD_create(dnf, order);
    clock_t end = clock();
    
    printf("Creation time: %.2f ms\n", (double)(end - start) * 1000 / CLOCKS_PER_SEC);
    printf("Node count: %d\n", bdd->node_count);
    
    int var_count = strlen(order);
    test_all_combinations(bdd, dnf, var_count);
    
    // Cleanup
    for (int i = 0; i < bdd->unique.size; i++) 
        free(bdd->unique.nodes[i]);
    free(bdd->unique.nodes);
    free(bdd->var_order);
    free(bdd);
}

void test_optimized_bdd(const char* dnf) {
    printf("Testing optimized BDD creation for DNF: %s\n", dnf);
    
    clock_t start = clock();
    BDD* bdd = BDD_create_with_best_order(dnf);
    clock_t end = clock();
    
    printf("Optimization time: %.2f ms\n", (double)(end - start) * 1000 / CLOCKS_PER_SEC);
    printf("Optimal order: %s\n", bdd->var_order);
    printf("Node count: %d\n", bdd->node_count);
    
    int var_count = strlen(bdd->var_order);
    test_all_combinations(bdd, dnf, var_count);
    
    // Cleanup
    for (int i = 0; i < bdd->unique.size; i++) 
        free(bdd->unique.nodes[i]);
    free(bdd->unique.nodes);
    free(bdd->var_order);
    free(bdd);
}


// -------------------- Main --------------------
int main() {
    srand(time(NULL));

    BDD *bdd = BDD_create_with_best_order("A!B!C+!AB!C+!A!BC");
    
    // Simple test cases
    test_bdd_creation("AB+!AC", "ABC");
    test_bdd_creation("A+B+C", "ABC");
    test_bdd_creation("A!B+!AB", "AB");
    
    // Test optimized creation
    test_optimized_bdd("AB+!AC");
    test_optimized_bdd("A+B+C");
    test_optimized_bdd("A!B+!AB");

    // Test with large DNFs
    test_bdd_creation("AMBLFG+JDBNHC+!AJ!EC+FIHMNE+KDH!LM+AK!BNG+E!HKAI+GJLNBE+!LDKEG+HGNKFD+FDCGJA+BJM!EA+!NIHMB+EJ!FAG+LGMBCD+BEGFIK+HMLDCG+B!NDHCM", "ABCDEFGHIJKLMN");
    test_optimized_bdd("AMBLFG+JDBNHC+!AJ!EC+FIHMNE+KDH!LM+AK!BNG+E!HKAI+GJLNBE+!LDKEG+HGNKFD+FDCGJA+BJM!EA+!NIHMB+EJ!FAG+LGMBCD+BEGFIK+HMLDCG+B!NDHCM");
    
    // Generate and test random DNFs
    for (int i = 0; i < 10; i++) {
        int var_count = 10 + rand() % 5; // 4-8 variables
        int term_count = 13 + rand() % 5; // 3-7 terms
        
        char* dnf = generate_random_dnf(var_count, term_count);
        
        // Create default order (alphabetical)
        char order[27] = {0};
        for (int j = 0; j < var_count; j++) {
            order[j] = 'A' + j;
        }
        
        test_bdd_creation(dnf, order);
        test_optimized_bdd(dnf);
        
        free(dnf);
    }
    
    return 0;
}