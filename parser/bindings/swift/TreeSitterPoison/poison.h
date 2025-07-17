#ifndef TREE_SITTER_POISON_H_
#define TREE_SITTER_POISON_H_

typedef struct TSLanguage TSLanguage;

#ifdef __cplusplus
extern "C" {
#endif

const TSLanguage *tree_sitter_poison(void);

#ifdef __cplusplus
}
#endif

#endif // TREE_SITTER_POISON_H_
