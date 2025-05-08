#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

// BDD node structure
typedef struct BDDNode {
    char var_name;          // Variable character (e.g., 'A', 'B')
    int var_index;          // Index in variable order (0-based)
    struct BDDNode *parent; // Parent node pointer
    struct BDDNode *then_branch; // Branch when variable = 1
    struct BDDNode *else_branch; // Branch when variable = 0
    int id;                 // Unique node identifier
    bool is_terminal;       // Terminal node flag
    char value;             // Terminal value ('0' or '1')
} BDDNode;

// Structure for storing unique nodes (for reduction)
typedef struct {
    BDDNode **nodes;        // Array of unique nodes
    int capacity;           // Current array capacity
    int size;               // Current number of nodes
} NodeDictionary;

// Main BDD structure
typedef struct {
    BDDNode *root;          // Root node of the BDD
    char *var_order;        // Variable order string (e.g., "BAC")
    int *var_priority;      // Priority array for sorting [A-Z] -> priority
    int var_count;          // Number of variables
    int node_count;         // Total nodes count
    NodeDictionary unique;  // Unique node table for reduction
} BDD;

// Initialize variable priority based on order
void init_var_priority(BDD *bdd) {
    bdd->var_priority = (int*)malloc(26 * sizeof(int)); // For A-Z
    for (int i = 0; i < bdd->var_count; i++) {
        // Higher index = lower priority in sorting
        bdd->var_priority[bdd->var_order[i] - 'A'] = bdd->var_count - i - 1;
    }
}

// Compare function for variable sorting based on priority
int compare_vars(const void *a, const void *b) {
    const char *ca = (const char*)a;
    const char *cb = (const char*)b;
    extern BDD *g_bdd; // Global access to BDD for priorities
    
    int prio_a = g_bdd->var_priority[*ca - 'A'];
    int prio_b = g_bdd->var_priority[*cb - 'A'];
    
    return prio_b - prio_a; // Sort descending by priority
}

// DNF term structure
typedef struct {
    char *variables;       // Sorted variables in term
    int length;            // Length of the term
} DNFTerm;

// Process DNF string into normalized terms
DNFTerm* normalize_dnf(const char *dnf, const char *var_order, int *term_count) {
    // Create temporary BDD for priority access
    BDD temp_bdd;
    temp_bdd.var_order = strdup(var_order);
    temp_bdd.var_count = strlen(var_order);
    init_var_priority(&temp_bdd);
    g_bdd = &temp_bdd; // Set global for compare function

    // Split into raw terms
    char *copy = strdup(dnf);
    *term_count = 1;
    for (char *p = copy; *p; p++) if (*p == '+') (*term_count)++;
    
    DNFTerm *terms = malloc(*term_count * sizeof(DNFTerm));
    char *term_str = strtok(copy, "+");
    
    for (int i = 0; term_str != NULL; i++) {
        // Remove whitespace and duplicates
        char cleaned[256] = {0};
        int pos = 0;
        
        for (char *p = term_str; *p; p++) {
            if (*p == ' ') continue;
            if (!strchr(cleaned, *p)) {
                cleaned[pos++] = *p;
            }
        }
        
        // Sort variables according to priority
        qsort(cleaned, pos, sizeof(char), compare_vars);
        
        // Store term
        terms[i].variables = strdup(cleaned);
        terms[i].length = pos;
        term_str = strtok(NULL, "+");
    }

    free(copy);
    free(temp_bdd.var_order);
    free(temp_bdd.var_priority);
    return terms;
}

// Example usage
int main() {
    const char *dnf = "CB + BA + ABC + CBA";
    const char *order = "BAC";
    
    int term_count;
    DNFTerm *terms = normalize_dnf(dnf, order, &term_count);
    
    printf("Original DNF: %s\n", dnf);
    printf("Variable order: %s\n", order);
    printf("Normalized terms:\n");
    for (int i = 0; i < term_count; i++) {
        printf("Term %d: %s\n", i+1, terms[i].variables);
        free(terms[i].variables);
    }
    
    free(terms);
    return 0;
}