

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>
#include <stdbool.h>

#include <containers/AAtree.h>
#include <debug/assert.h>
#include <memory.h>


struct AAnode
{
    int level;
    void* data;
    struct AAnode* parent;
    struct AAnode* left;
    struct AAnode* right;
};


struct AAtree
{
    AAnode* nil;
    AAnode* root;
    int (*cmp)(const void*, const void*);
    void (*destroy)(void*);
};


static AAnode* aapred(AAnode* node);

static AAnode* aasucc(AAnode* node);

static AAnode* aaskew(AAnode* root);

static AAnode* aasplit(AAnode* root);

static void aafree(AAnode* node, void (*destroy)(void*));

#ifndef NDEBUG
#define aavalidate(node, msg) (assert(aavalidate_(node, msg)))
static bool aavalidate_(const AAnode* node, const char* msg);
#else
#define aavalidate(node, msg) (void)0
#endif


AAiter* new_AAiter(AAtree* tree)
{
    AAiter* iter = memory_alloc_item(AAiter);
    if (iter == NULL)
        return NULL;

    iter->tree = tree;
    iter->node = NULL;
    return iter;
}


void AAiter_change_tree(AAiter* iter, const AAtree* tree)
{
    assert(iter != NULL);
    assert(tree != NULL);

    iter->tree = tree;
    iter->node = NULL;

    return;
}


void del_AAiter(AAiter* iter)
{
    memory_free(iter);
    return;
}


static AAnode* new_AAnode(AAnode* nil, void* data)
{
    assert(!(nil == NULL) || (data == NULL));
    assert(!(data == NULL) || (nil == NULL));

    AAnode* node = memory_alloc_item(AAnode);
    if (node == NULL)
        return NULL;

    if (nil == NULL)
    {
        assert(data == NULL);
        node->data = NULL;
        node->level = 0;
        node->parent = node->left = node->right = node;
    }
    else
    {
        assert(data != NULL);
        node->data = data;
        node->level = 1;
        node->parent = node->left = node->right = nil;
    }

    return node;
}


void* AAnode_get_data(AAnode* node)
{
    assert(node != NULL);
    return node->data;
}


AAtree* new_AAtree(int (*cmp)(const void*, const void*), void (*destroy)(void*))
{
    assert(cmp != NULL);
    assert(destroy != NULL);

    AAtree* tree = memory_alloc_item(AAtree);
    if (tree == NULL)
        return NULL;

    tree->nil = new_AAnode(NULL, NULL);
    if (tree->nil == NULL)
    {
        memory_free(tree);
        return NULL;
    }

    tree->root = tree->nil;
    tree->cmp = cmp;
    tree->destroy = destroy;
    aavalidate(tree->root, "init");

    return tree;
}


bool AAtree_contains(const AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);

    return (AAtree_get_exact(tree, key) != NULL);
}


bool AAtree_ins(AAtree* tree, void* data)
{
    assert(tree != NULL);
    assert(data != NULL);
    assert(!AAtree_contains(tree, data));

    AAnode* node = new_AAnode(tree->nil, data);
    if (node == NULL)
        return false;

    AAtree_attach(tree, node);

    return true;
}


void AAtree_attach(AAtree* tree, AAnode* node)
{
    assert(tree != NULL);
    assert(node != NULL);
    assert(node->data != NULL);

    // Make the node ours
    node->parent = node->left = node->right = tree->nil;

    aavalidate(tree->root, "before insert");

    if (tree->root->level == 0)
    {
        tree->root = node;
        aavalidate(tree->root, "insert root");
        return;
    }

    AAnode* cur = tree->root;
    AAnode* prev = NULL;
    assert(cur->data != NULL);
    int diff = 1;
    while (cur->level > 0 && diff != 0)
    {
        assert(cur->data != NULL);
        diff = tree->cmp(node->data, cur->data);
        prev = cur;

        if (diff < 0)
            cur = cur->left;
        else if (diff > 0)
            cur = cur->right;
    }

    assert(prev != NULL);

    assert(diff != 0);
#if 0
    if (diff == 0)
    {
        assert(cur != NULL);
        assert(cur->data != NULL);
        tree->destroy(cur->data);
        cur->data = data;
        aavalidate(tree->root, "insert");
        return true;
    }
#endif

    // Attach the new node
    if (diff < 0)
    {
        assert(prev->left->level == 0);
        prev->left = node;
        node->parent = prev;
    }
    else
    {
        assert(diff > 0);
        assert(prev->right->level == 0);
        prev->right = node;
        node->parent = prev;
    }

    cur = node->parent;
    while (cur->level > 0)
    {
        AAnode* parent = cur->parent;
        AAnode** child = NULL;

        if (parent->left == cur)
            child = &parent->left;
        else if (parent->right == cur)
            child = &parent->right;
        else
        {
            assert(parent->level == 0);
            child = &tree->root;
        }

        assert(child != NULL);
        cur = aaskew(cur);
        cur = aasplit(cur);
        aavalidate(cur, "balance");
        *child = cur;
        cur = cur->parent;
    }

    aavalidate(tree->root, "insert rebalance");
    return;
}


void* AAiter_get_at_least(AAiter* iter, const void* key)
{
    assert(iter != NULL);
    assert(key != NULL);
    assert(iter->tree != NULL);

    const AAtree* tree = iter->tree;
    aavalidate(tree->root, "get");
    AAnode** last = &iter->node;
    *last = NULL;
    AAnode* ret = tree->nil;
    AAnode* cur = tree->root;

    while (cur->level > 0)
    {
        assert(cur->data != NULL);
        int diff = tree->cmp(key, cur->data);
        if (diff < 0)
        {
            ret = cur;
            *last = cur;
            cur = cur->left;
        }
        else if (diff > 0)
        {
            cur = cur->right;
        }
        else
        {
            *last = cur;
            return cur->data;
        }
    }

    return ret->data;
}


void* AAtree_get_at_least(const AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);

    AAiter* iter = AAITER_AUTO;
    iter->tree = tree;

    return AAiter_get_at_least(iter, key);
}


void* AAtree_get_exact(const AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);

    AAiter* iter = AAITER_AUTO;
    iter->tree = tree;
    void* ret = AAiter_get_at_least(iter, key);
    if (ret != NULL && tree->cmp(ret, key) == 0)
        return ret;

    return NULL;
}


void* AAiter_get_at_most(AAiter* iter, const void* key)
{
    assert(iter != NULL);
    assert(key != NULL);
    assert(iter->tree != NULL);

    const AAtree* tree = iter->tree;
    aavalidate(tree->root, "get");
    AAnode** last = &iter->node;
    *last = NULL;
    AAnode* ret = tree->nil;
    AAnode* cur = tree->root;

    while (cur->level > 0)
    {
        assert(cur->data != NULL);
        int diff = tree->cmp(key, cur->data);
        if (diff < 0)
        {
            cur = cur->left;
        }
        else if (diff > 0)
        {
            ret = cur;
            *last = cur;
            cur = cur->right;
        }
        else
        {
            *last = cur;
            return cur->data;
        }
    }

    return ret->data;
}


void* AAtree_get_at_most(const AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);

    AAiter* iter = AAITER_AUTO;
    iter->tree = tree;

    return AAiter_get_at_most(iter, key);
}


void* AAiter_get_next(AAiter* iter)
{
    assert(iter != NULL);
    assert(iter->tree != NULL);

    if (iter->node == NULL)
        return NULL;

    const AAtree* tree = iter->tree;
    if (iter->node == tree->nil)
        return NULL;

    iter->node = aasucc(iter->node);
    if (iter->node == tree->nil)
        return NULL;

    return iter->node->data;
}


void* AAiter_get_prev(AAiter* iter)
{
    assert(iter != NULL);
    assert(iter->tree != NULL);

    if (iter->node == NULL)
        return NULL;

    const AAtree* tree = iter->tree;
    if (iter->node == tree->nil)
        return NULL;

    iter->node = aapred(iter->node);
    if (iter->node == tree->nil)
        return NULL;

    return iter->node->data;
}


AAnode* AAtree_detach(AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);
    assert(tree->root->parent == tree->nil);

    if (tree->root->level == 0)
        return NULL;

    AAnode* cur = tree->root;
    int diff = 1;
    while (cur->level > 0 && diff != 0)
    {
        diff = tree->cmp(key, cur->data);
        if (diff < 0)
            cur = cur->left;
        else if (diff > 0)
            cur = cur->right;
    }

    assert(cur != NULL);
    if (cur->level == 0)
        return NULL;

    // Get data so that we can assign it to another node if needed
    void* data = cur->data;
    cur->data = NULL;

    if (cur->left->level != 0 && cur->right->level != 0)
    {
        assert(cur->left->level > 0);
        assert(cur->right->level > 0);
        AAnode* pred = aapred(cur);
        assert(pred != NULL);
        assert(pred->right->level == 0);
        cur->data = pred->data;
        pred->data = NULL;
        cur = pred;
    }

    assert(cur->left->level == 0 || cur->right->level == 0);
    AAnode** child = NULL;
    AAnode* parent = cur->parent;
    if (cur == cur->parent->left)
    {
        child = &cur->parent->left;
    }
    else if (cur == cur->parent->right)
    {
        child = &cur->parent->right;
    }
    else
    {
        assert(cur == tree->root);
        child = &tree->root;
        parent = tree->nil;
    }

    assert(child != NULL);
    if (cur->left->level > 0)
    {
        assert(cur->right->level == 0);
        *child = cur->left;
        cur->left->parent = parent;
    }
    else
    {
        *child = cur->right;
        cur->right->parent = parent;
    }

    AAnode* node = cur->parent;

    // Set up the node to be returned
    AAnode* ret = cur;
    ret->left = ret->right = NULL;
    ret->data = data;

    // Balance
    cur = node;
    while (cur->level > 0)
    {
        parent = cur->parent;
        child = NULL;

        if (parent->left == cur)
            child = &parent->left;
        else if (parent->right == cur)
            child = &parent->right;
        else
        {
            assert(parent->level == 0);
            child = &tree->root;
        }

        if (cur->left->level < cur->level - 1
                || cur->right->level < cur->level - 1)
        {
            --cur->level;
            if (cur->right->level > cur->level)
                cur->right->level = cur->level;

            assert(child != NULL);
            cur = aaskew(cur);
            cur = aasplit(cur);
            *child = cur;
        }

        aavalidate(cur, "balance");
        cur = cur->parent;
    }

    aavalidate(tree->root, "remove");
    return ret;
}


void* AAtree_remove(AAtree* tree, const void* key)
{
    assert(tree != NULL);
    assert(key != NULL);
    assert(tree->root->parent == tree->nil);

    AAnode* node = AAtree_detach(tree, key);
    if (node == NULL)
        return NULL;

    void* data = node->data;
    memory_free(node);

    return data;
}


void AAtree_clear(AAtree* tree)
{
    assert(tree != NULL);
    aavalidate(tree->root, "clear");

    if (tree->root != tree->nil)
    {
        aafree(tree->root, tree->destroy);
        tree->root = tree->nil;
    }

    return;
}


void del_AAtree(AAtree* tree)
{
    if (tree == NULL)
        return;

    aavalidate(tree->root, "del");
    AAtree_clear(tree);
    memory_free(tree->nil);
    memory_free(tree);

    return;
}


static AAnode* aapred(AAnode* node)
{
    assert(node != NULL);
    assert(node->level > 0);

    if (node->left->level > 0)
    {
        node = node->left;

        while (node->right->level > 0)
            node = node->right;

        return node;
    }

    AAnode* prev = node;
    node = node->parent;
    while (prev == node->left)
    {
        prev = node;
        node = node->parent;
    }

    return node;
}


static AAnode* aasucc(AAnode* node)
{
    assert(node != NULL);

    if (node->level == 0)
        return node;

    if (node->right->level > 0)
    {
        node = node->right;
        while (node->left->level > 0)
            node = node->left;

        return node;
    }

    AAnode* prev = node;
    node = node->parent;
    while (prev == node->right)
    {
        prev = node;
        node = node->parent;
    }

    return node;
}


static AAnode* aaskew(AAnode* root)
{
    assert(root != NULL);

    if (root->level == 0)
        return root;

    if (root->left->level == root->level)
    {
        AAnode* new_root = root->left;
        root->left = new_root->right;
        new_root->right = root;
        root->left->parent = root;
        new_root->parent = root->parent;
        root->parent = new_root;
        root = new_root;
    }

    root->right = aaskew(root->right);

    return root;
}


static AAnode* aasplit(AAnode* root)
{
    assert(root != NULL);

    if (root->level == 0)
        return root;

    if (root->level == root->right->right->level)
    {
        AAnode* new_root = root->right;
        root->right = new_root->left;
        new_root->left = root;
        root->right->parent = root;
        new_root->parent = root->parent;
        root->parent = new_root;
        root = new_root;
        ++root->level;
        root->right = aasplit(root->right);
    }

    return root;
}


static void aafree(AAnode* node, void (*destroy)(void*))
{
    assert(node != NULL);
    assert(destroy != NULL);

    if (node->level == 0)
        return;

    aafree(node->left, destroy);
    aafree(node->right, destroy);
    destroy(node->data);
    memory_free(node);

    return;
}


#ifndef NDEBUG
static bool aavalidate_(const AAnode* node, const char* msg)
{
    if (node == NULL
            || node->parent == NULL
            || node->left == NULL
            || node->right == NULL)
        return false;

/*  fprintf(stderr, "level %d: parent: %6lx, left: %6lx, this: %6lx, right: %6lx\n",
            node->level,
            (long)node->parent % (long)nil,
            (long)node->left % (long)nil,
            (long)node % (long)nil,
            (long)node->right % (long)nil); */

    if (node->level == 0)
    {
        if (node->data != NULL)
            return false;
        if (node->left != node)
            return false;
        if (node->right != node)
            return false;
        return true;
    }

    if (node->left == node)
        return false;
    if (node->right == node)
        return false;
    if (node->parent == node)
        return false;

    if (node->left->level > 0 && node->left->parent != node)
        return false;
    if (node->right->level > 0 && node->right->parent != node)
        return false;
    if (node->level != node->left->level + 1)
        return false;
    if (node->level == node->right->right->level)
        return false;
    if (node->level != node->right->level
            && node->level != node->right->level + 1)
        return false;

    if (node->data == NULL)
        return false;

    if (aavalidate_(node->left, msg) && aavalidate_(node->right, msg))
        return true;

    return false;
}
#endif


