#include <iostream>
#include <vector>
#include <algorithm>
#include <cassert>
#include <ctime>
#include <random>
#include <tuple>
#include <functional>
#include <iterator>
#include <fstream>

class DefaultRandomIntegerGenerator {
    std::mt19937 gen;
    std::uniform_int_distribution<int> uid;
public:
    DefaultRandomIntegerGenerator() : gen(time_t(0)), uid(INT32_MIN, INT32_MAX) {}

    int next() {
        return uid(gen);
    }

};

template<class RandomIntegerGenerator = DefaultRandomIntegerGenerator>
class Cartesian_Tree {
private:
    struct Node {
        int prior;
        long long value, LeftValue, RightValue, PushInSegment, SummSegment;
        bool isOrdered, isReverseOrdered;
        bool ReverseSegment;
        bool NeedSetZero;
        size_t cnt;
        Node *l, *r;

        explicit Node(long long Value, int prior) : prior(prior), value(Value), LeftValue(Value), RightValue(Value),
                                                    isOrdered(true), isReverseOrdered(true), ReverseSegment(false),
                                                    NeedSetZero(false),
                                                    SummSegment(Value), PushInSegment(0), cnt(1), l(nullptr),
                                                    r(nullptr) {}

        ~Node() {
            delete l;
            delete r;
        }
    };

    typedef std::tuple<Node *, Node *> pair_trees;
    typedef std::tuple<Node *, Node *, Node *> triplet_trees;

    template<typename U>
    static void myswap(U &x, U &y) {
        U tmp = std::move(x);
        x = std::move(y);
        y = std::move(tmp);
    }

    RandomIntegerGenerator generator;
    Node *Root_;

    static size_t cnt_(Node *t) {
        return (!t ? 0 : t->cnt);
    }

    static void recalc_Add_(Node *t, long long x) {
        if (!t)return;
        t->value += x;
        t->SummSegment += x * cnt_(t);
        t->LeftValue += x;
        t->RightValue += x;
    }

    static void recalc_SetZero_(Node *t) {
        if (!t)return;
        t->value = t->LeftValue = t->RightValue = t->SummSegment = 0;
        t->PushInSegment = 0;
        t->isOrdered = t->isReverseOrdered = true;
    }

    static void recalc_Push_(Node *t) {
        if (!t)return;
        myswap(t->isOrdered, t->isReverseOrdered);
        myswap(t->LeftValue, t->RightValue);
        myswap(t->l, t->r);
    }

    static void push_Reverse_(Node *t) {
        if (t->ReverseSegment) {
            recalc_Push_(t->l);
            recalc_Push_(t->r);
            if (t->l)t->l->ReverseSegment ^= true;
            if (t->r)t->r->ReverseSegment ^= true;
            t->ReverseSegment = false;
        }
    }

    static void push_SetZero_(Node *t) {
        if (t->NeedSetZero) {
            recalc_SetZero_(t->l);
            recalc_SetZero_(t->r);
            if (t->l)t->l->NeedSetZero = true;
            if (t->r)t->r->NeedSetZero = true;
            t->NeedSetZero = false;
        }
    }

    static void push_Add_(Node *t) {
        if (t->PushInSegment != 0) {
            recalc_Add_(t->l, t->PushInSegment);
            recalc_Add_(t->r, t->PushInSegment);
            if (t->l)t->l->PushInSegment += t->PushInSegment;
            if (t->r)t->r->PushInSegment += t->PushInSegment;
            t->PushInSegment = 0;
        }
    }

    static void push_(Node *t) {
        if (!t)return;
        push_Reverse_(t);
        push_SetZero_(t);
        push_Add_(t);
    }

    static void update_(Node *t) {
        if (!t)return;
        push_(t->l);
        push_(t->r);
        t->cnt = 1 + cnt_(t->l) + cnt_(t->r);
        t->isOrdered = (t->l ? t->l->isOrdered : true) & (t->r ? t->r->isOrdered : true) &
                       (t->l ? t->l->RightValue <= t->value : true) & (t->r ? t->value <= t->r->LeftValue : true);
        t->isReverseOrdered = (t->l ? t->l->isReverseOrdered : true) & (t->r ? t->r->isReverseOrdered : true) &
                              (t->l ? t->l->RightValue >= t->value : true) &
                              (t->r ? t->value >= t->r->LeftValue : true);

        t->LeftValue = (t->l ? t->l->LeftValue : t->value);
        t->RightValue = (t->r ? t->r->RightValue : t->value);
        t->SummSegment = t->value + (t->l ? t->l->SummSegment : 0) + (t->r ? t->r->SummSegment : 0);
    }

    static void modify_Tree_Add_(Node *t, long long x) {
        if (!t)return;
        t->PushInSegment += x;
        recalc_Add_(t, x);
    }

    static void modify_Tree_Set_(Node *t, long long x) {
        if (!t)return;
        t->NeedSetZero = true;
        recalc_SetZero_(t);
        t->PushInSegment = x;
        recalc_Add_(t, x);
    }

    static void modify_Tree_Reverse_(Node *t) {
        if (!t)return;
        t->ReverseSegment = true;
        recalc_Push_(t);
    }

    template<bool isImplicit = true, typename key_type = size_t>
    static pair_trees split_(Node *t, key_type key, size_t add = 0) {
        if (t == nullptr) {
            return pair_trees(nullptr, nullptr);
        }
        push_(t);
        key_type curKey = (isImplicit ? add + cnt_(t->l) : t->value - 1);
        if (key <= curKey) {
            Node *left, *right;
            std::tie(left, right) = split_<isImplicit, key_type>(t->l, key, add);
            t->l = right;
            update_(t);
            return pair_trees(left, t);
        } else {
            Node *left, *right;
            std::tie(left, right) = split_<isImplicit, key_type>(t->r, key, add + 1 + cnt_(t->l));
            t->r = left;
            update_(t);
            return pair_trees(t, right);
        }
    }

    static triplet_trees splitOn3Segments_(Node *Root, size_t l, size_t r) {
        Node *left, *middle, *right;
        std::tie(middle, right) = split_(Root, r + 1);
        std::tie(left, middle) = split_(middle, l);
        return triplet_trees(left, middle, right);
    }

    static Node *merge_(std::vector<Node *> allRoots) {
        assert(!allRoots.empty());
        for (size_t i = 1; i < allRoots.size(); ++i) {
            allRoots[0] = merge_(allRoots[0], allRoots[i]);
        }
        return allRoots[0];
    }

    static Node *merge_(Node *l, Node *r) {
        push_(l);
        push_(r);
        if (!l)return r;
        else if (!r)return l;
        else if (l->prior > r->prior) {
            l->r = merge_(l->r, r);
            update_(l);
            return l;
        } else {
            r->l = merge_(l, r->l);
            update_(r);
            return r;
        }
    }

    static size_t findLenSuffix_(Node *t, bool isOrderedSuffix) {
        if (t == nullptr)return 0;
        push_(t);
        if (t->r && (isOrderedSuffix ? !t->r->isOrdered : !t->r->isReverseOrdered)) {
            return 1 + cnt_(t->l) + findLenSuffix_(t->r, isOrderedSuffix);
        }
        if (t->r && (isOrderedSuffix ? t->value > t->r->LeftValue : t->value < t->r->LeftValue)) {
            return 1 + cnt_(t->l);
        }
        if (t->l && (isOrderedSuffix ? t->value < t->l->RightValue : t->value > t->l->RightValue)) {
            return cnt_(t->l);
        }
        return findLenSuffix_(t->l, isOrderedSuffix);
    }

    void out_(Node *t, std::vector<long long> &Result) {
        if (!t)return;
        push_(t);
        out_(t->l, Result);
        Result.push_back(t->value);
        out_(t->r, Result);
    }

    template<bool isPrev>
    static Node *permutation_(Node *Segment) {
        if (isPrev ? Segment->isOrdered : Segment->isReverseOrdered) {
            modify_Tree_Reverse_(Segment);
            return Segment;
        }
        size_t len = findLenSuffix_(Segment, isPrev);
        Node *tLeft, *NowNode, *tRight, *tRight_Left, *tRight_Right, *SwapElement;
        std::tie(tLeft, NowNode, tRight) = splitOn3Segments_(Segment, len - 1, len - 1);

        if (isPrev) {
            std::tie(tRight_Left, tRight_Right) = split_<false>(tRight, NowNode->value - 1);
            std::tie(tRight_Left, SwapElement) = split_(tRight_Left, cnt_(tRight_Left) - 1);
            modify_Tree_Reverse_(tRight_Right);
            modify_Tree_Reverse_(tRight_Left);
        } else {
            modify_Tree_Reverse_(tRight);
            std::tie(tRight_Left, tRight_Right) = split_<false>(tRight, NowNode->value);
            std::tie(SwapElement, tRight_Right) = split_(tRight_Right, 1);
            myswap(tRight_Left, tRight_Right);
        }
        Segment = merge_({tLeft, SwapElement, tRight_Right, NowNode, tRight_Left});
        return Segment;
    }

    template<typename Func>
    Node *makeOperationOnSubsegment_(size_t l, size_t r, Func f) {
        Node *Left, *Segment, *Right;
        std::tie(Left, Segment, Right) = splitOn3Segments_(Root_, l, r);
        Segment = f(Segment);
        Root_ = merge_({Left, Segment, Right});
    }

public:
    Cartesian_Tree() : Root_(nullptr), generator(RandomIntegerGenerator()) {}

    ~Cartesian_Tree() {
        delete Root_;
    }

    long long SummInSegment(size_t l, size_t r) {
        long long Summ = 0;
        makeOperationOnSubsegment_(l, r, [&Summ](Node *Segment) -> Node * {
            Summ = Segment->SummSegment;
            return Segment;
        });
        return Summ;
    }

    void Insert(size_t pos, long long x) {
        int prior = generator.next();
        makeOperationOnSubsegment_(pos, pos - 1, [&prior, &x](Node *Segment) -> Node * {
            assert(Segment == nullptr);
            return new Node(x, prior);
        });
    }

    void Remove(size_t pos) {
        makeOperationOnSubsegment_(pos, pos, [](Node *Segment) -> Node * {
            delete Segment;
            return nullptr;
        });
    }

    void Add(long long x, size_t l, size_t r) {
        makeOperationOnSubsegment_(l, r, [&x](Node *Segment) -> Node * {
            Cartesian_Tree::modify_Tree_Add_(Segment, x);
            return Segment;
        });
    }

    void Set(long long x, size_t l, size_t r) {
        makeOperationOnSubsegment_(l, r, [&x](Node *Segment) -> Node * {
            Cartesian_Tree::modify_Tree_Set_(Segment, x);
            return Segment;
        });
    }

    void NextPermutation(size_t l, size_t r) {
        makeOperationOnSubsegment_(l, r, [](Node *Segment) -> Node * {
            Segment = Cartesian_Tree::permutation_<false>(Segment);
            return Segment;
        });
    }

    void PrevPermutation(size_t l, size_t r) {
        makeOperationOnSubsegment_(l, r, [](Node *Segment) -> Node * {
            Segment = Cartesian_Tree::permutation_<true>(Segment);
            return Segment;
        });
    }

    void GetAllElements(std::vector<long long> &Result) {
        out_(Root_, Result);
    }
};

struct Output {
    std::vector<long long> SummAnswers;
    std::vector<long long> Result;

    Output() {}

    void add_summ(long long x) {
        SummAnswers.push_back(x);
    }

    void add_result(long long x) {
        Result.push_back(x);
    }

    std::vector<long long>::iterator beginSummIterator() {
        return SummAnswers.begin();
    }

    std::vector<long long>::iterator endSummIterator() {
        return SummAnswers.end();
    }

    std::vector<long long>::iterator beginResult() {
        return Result.begin();
    }

    std::vector<long long>::iterator endResult() {
        return Result.end();
    }
};

struct Query {
    Query() {}

    virtual void execute(Cartesian_Tree<> &Tree, Output &out) = 0;

    virtual Query *copy() = 0;
};

struct ModifyWithoutParameterQuery : public Query {
    ModifyWithoutParameterQuery(size_t l, size_t r) : l(l), r(r) {}

protected:
    size_t l, r;
};

struct SummQuery : public ModifyWithoutParameterQuery {
    SummQuery(size_t l, size_t r) : ModifyWithoutParameterQuery(l, r) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        out.add_summ(Tree.SummInSegment(l, r));
    }

    SummQuery *copy() override {
        return new SummQuery(l, r);
    }
};

struct NextPermutationQuery : public ModifyWithoutParameterQuery {
    NextPermutationQuery(size_t l, size_t r) : ModifyWithoutParameterQuery(l, r) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.NextPermutation(l, r);
    }

    NextPermutationQuery *copy() override {
        return new NextPermutationQuery(l, r);
    }
};

struct PrevPermutationQuery : public ModifyWithoutParameterQuery {
    PrevPermutationQuery(size_t l, size_t r) : ModifyWithoutParameterQuery(l, r) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.PrevPermutation(l, r);
    }

    PrevPermutationQuery *copy() override {
        return new PrevPermutationQuery(l, r);
    }
};

struct InsertQuery : public Query {
    InsertQuery(size_t pos, long long x) : pos(pos), x(x) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.Insert(pos, x);
    }

    InsertQuery *copy() override {
        return new InsertQuery(pos, x);
    }

private:
    size_t pos;
    long long x;
};

struct RemoveQuery : public Query {
    RemoveQuery(size_t pos) : pos(pos) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.Remove(pos);
    }

    RemoveQuery *copy() override {
        return new RemoveQuery(pos);
    }

private:
    size_t pos;
};

struct ModifyWithParameterQuery : public Query {
    ModifyWithParameterQuery(long long x, size_t l, size_t r) : l(l), r(r), x(x) {}

protected:
    size_t l, r;
    long long x;
};

struct SetQuery : public ModifyWithParameterQuery {
    SetQuery(long long x, size_t l, size_t r) : ModifyWithParameterQuery(x, l, r) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.Set(x, l, r);
    }

    SetQuery *copy() override {
        return new SetQuery(x, l, r);
    }
};

struct AddQuery : public ModifyWithParameterQuery {
    AddQuery(long long x, size_t l, size_t r) : ModifyWithParameterQuery(x, l, r) {}

    void execute(Cartesian_Tree<> &Tree, Output &out) override {
        Tree.Add(x, l, r);
    }

    AddQuery *copy() override {
        return new AddQuery(x, l, r);
    }
};

class Input {
    std::vector<long long> elements_;
    std::vector<Query *> q_;
public:
    Input() {}

    ~Input() {
        for (size_t i = 0; i < q_.size(); ++i) {
            delete q_[i];
        }
    }

    Input &operator=(const Input &b) {
        if (&b == this)return *this;
        elements_ = b.elements_;
        for (auto q : b.q_) {
            q_.push_back(q->copy());
        }
        return *this;
    }

    void add_query(Query *q) {
        q_.push_back(q);
    }

    void add_element(long long x) {
        elements_.push_back(x);
    }

    std::vector<Query *>::iterator beginQueryIterator() {
        return q_.begin();
    }

    std::vector<Query *>::iterator endQueryIterator() {
        return q_.end();
    }

    std::vector<long long>::iterator beginElementItaretor() {
        return elements_.begin();
    }

    std::vector<long long>::iterator endElementIterator() {
        return elements_.end();
    }
};

Output solve(Input &in) {
    Cartesian_Tree<> Tree = Cartesian_Tree<>();
    size_t pos = 0;
    for (auto it = in.beginElementItaretor(); it != in.endElementIterator(); ++pos, ++it) {
        Tree.Insert(pos, *it);
    }
    Output out;
    for (auto it = in.beginQueryIterator(); it != in.endQueryIterator(); ++it) {
        (*it)->execute(Tree, out);
    }
    Tree.GetAllElements(out.Result);
    return out;
}

void read_array(std::istream &from, Input &in) {
    size_t n;
    from >> n;
    for (size_t i = 0; i < n; ++i) {
        long long x;
        from >> x;
        in.add_element(x);
    }
}

void read_queries(std::istream &from, Input &in) {
    size_t m;
    from >> m;
    enum {
        SummOnSegment = 1, Insert, Remove, Set, Add, NextPermutation, PrevPermutation
    };
    for (int i = 1; i <= m; ++i) {
        size_t type, pos, l, r;
        long long x;
        from >> type;
        Query *q;
        switch (type) {
            case SummOnSegment:
                from >> l >> r;
                q = new SummQuery(l, r);
                break;
            case Insert:
                from >> x >> pos;
                q = new InsertQuery(pos, x);
                break;
            case Remove:
                from >> pos;
                q = new RemoveQuery(pos);
                break;
            case Set:
                from >> x >> l >> r;
                q = new SetQuery(x, l, r);
                break;
            case Add:
                from >> x >> l >> r;
                q = new AddQuery(x, l, r);
                break;
            case NextPermutation:
                from >> l >> r;
                q = new NextPermutationQuery(l, r);
                break;
            case PrevPermutation:
                from >> l >> r;
                q = new PrevPermutationQuery(l, r);
                break;
            default:
                break;
        }
        in.add_query(q);
    }
}

Input read(std::istream &from) {
    Input in;
    read_array(from, in);
    read_queries(from, in);
    return in;
}

void write_by_vector_iterator(std::ostream &into, std::vector<long long>::iterator begin,
                              std::vector<long long>::iterator end, char delimitter) {
    for (auto it = begin; it != end; ++it) {
        into << *it << delimitter;
    }
}

void write(std::ostream &into, Output &out) {
    write_by_vector_iterator(into, out.beginSummIterator(), out.endSummIterator(), '\n');
    write_by_vector_iterator(into, out.beginResult(), out.endResult(), ' ');
}

int main() {
    Input in = read(std::cin);
    Output out = solve(in);
    write(std::cout, out);
}