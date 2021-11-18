#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <set>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <queue>
#include <chrono>
#include <map>
#include <climits>
#include <algorithm>
#include <random>
using namespace std;

typedef pair<int, int> PII;

/**
 * @brief Get the Graph object
 * 
 * @param filename Graph data file
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 */
void getGraph(const string &filename, vector<vector<int>> &hyperEdge, unordered_map<int, vector<int>> &hyperNode)
{
    ifstream fin(filename, ios::in);
    int count = -1;
    while (true)
    {
        string str;
        getline(fin, str);
        if (str == "")
            break;
        istringstream ss(str);
        int tmp;
        vector<int> e;
        while (ss >> tmp)
        {
            if (find(e.begin(), e.end(), tmp) == e.end())
                e.push_back(tmp);
        }
        if (e.size() == 1)
            continue;
        count++;
        hyperEdge.push_back(e);
        for (auto &node : e)
            hyperNode[node].push_back(count);
    }
}

/**
 * @brief Arrange the pair.second in ascending order
 * 
 */
struct myCmp
{
    bool operator()(const pair<int, int> &a, const pair<int, int> &b) const
    {
        if (a.first == b.first)
            return false;
        else
        {
            if (a.second != b.second)
                return a.second < b.second;
            else
                return a.first < b.first;
        }
    }
};

/**
 * @brief Arrange the pair.second in descending order
 * 
 */
struct cmp
{
    bool operator()(const PII &a, const PII &b) const
    {
        return a.second > b.second;
    }
};

/**
 * @brief Hash of pair
 * 
 */
struct hashPair
{
    size_t operator()(const pair<int, int> &p) const
    {
        return hash<int>()(p.first) & hash<int>()(p.second);
    }
};

/**
 * @brief Equal of pair
 * 
 */
struct pair_equal
{
    bool operator()(const pair<int, int> &a, const pair<int, int> &b) const
    {
        return a.first == b.first && a.second == b.second;
    }
};

/**
 * @brief Kh-core decomposition of hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core Kh-core value of hypernode
 */
void khCoreDecomp(const vector<vector<int>> &hyperEdge, const unordered_map<int, vector<int>> &hyperNode, unordered_map<int, pair<int, int>> &core)
{
    core.clear();
    set<pair<int, int>, myCmp> node_count;
    unordered_map<int, int> degEdge;
    vector<bool> visitEdge(hyperEdge.size(), false);
    unordered_map<int, bool> visitNode;
    unordered_map<int, unordered_map<int, int>> nbr;
    unordered_map<int, bool> hvisitNode;
    set<pair<int, int>, myCmp> s;
    for (auto &it : hyperNode)
    {
        for (auto &edge : it.second)
        {
            for (auto &node : hyperEdge.at(edge))
            {
                nbr[it.first][node]++;
            }
        }
        degEdge[it.first] = it.second.size();
        node_count.insert(make_pair(it.first, degEdge[it.first]));
        visitNode[it.first] = false;
        nbr[it.first].erase(it.first);
        s.insert(make_pair(it.first, nbr[it.first].size()));
    }
    int K = 0;
    vector<int> visitEdgeTmp(hyperEdge.size(), false);
    while (!node_count.empty())
    {
        pair<int, int> p = *node_count.begin();
        node_count.erase(node_count.begin());
        if (K < p.second)
        {
            int k = 0;
            int count = 0;
            for (auto &it : core)
            {
                if (it.second.first == K)
                    count++;
            }
            vector<int> joinagain;
            while (!s.empty() && count != 0)
            {
                pair<int, int> pp = *s.begin();
                s.erase(s.begin());
                k = max(k, pp.second);
                if (core.find(pp.first) == core.end())
                {
                    joinagain.push_back(pp.first);
                }
                else if (core[pp.first].first == K)
                {
                    hvisitNode[pp.first] = true;
                    count--;
                    core[pp.first].second = k;
                }

                for (auto &edge : hyperNode.at(pp.first))
                {
                    if (visitEdgeTmp[edge])
                        continue;
                    visitEdgeTmp[edge] = true;

                    for (int i = 0; i < hyperEdge.at(edge).size(); i++)
                    {
                        int v = hyperEdge.at(edge).at(i);
                        if (v == pp.first)
                            continue;
                        s.erase(make_pair(v, nbr[v].size()));
                        for (int j = 0; j < hyperEdge.at(edge).size(); j++)
                        {

                            int u = hyperEdge.at(edge).at(j);
                            if (v == u)
                                continue;
                            if (nbr[v].find(u) != nbr[v].end())
                                nbr[v][u]--;
                            if (nbr[v][u] == 0)
                                nbr[v].erase(u);
                        }
                        s.insert(make_pair(v, nbr[v].size()));
                    }
                }
                nbr[pp.first].clear();
            }
            for (auto &it : joinagain)
            {

                for (auto &edge : hyperNode.at(it))
                {
                    if (!visitEdgeTmp[edge])
                        continue;
                    bool flag = false;
                    for (auto &node : hyperEdge.at(edge))
                        if (hvisitNode[node])
                        {
                            flag = true;
                            break;
                        }
                    if (flag)
                        continue;
                    for (int i = 0; i < hyperEdge.at(edge).size(); i++)
                    {
                        int v = hyperEdge.at(edge).at(i);
                        for (int j = 0; j < hyperEdge.at(edge).size(); j++)
                        {

                            int u = hyperEdge.at(edge).at(j);
                            if (v == u)
                                continue;
                            s.erase(make_pair(v, nbr[v].size()));
                            nbr[v][u]++;
                            s.insert(make_pair(v, nbr[v].size()));
                        }
                    }
                    visitEdgeTmp[edge] = false;
                }
            }
        }
        K = max(K, p.second);
        core[p.first].first = K;
        visitNode.at(p.first) = true;
        for (auto &edge : hyperNode.at(p.first))
        {
            if (visitEdge[edge])
                continue;
            visitEdge[edge] = true;
            for (auto &node : hyperEdge.at(edge))
            {
                if (visitNode[node])
                    continue;
                node_count.erase(make_pair(node, degEdge[node]));
                degEdge[node]--;
                node_count.insert(make_pair(node, degEdge[node]));
            }
        }
    }
    {
        int k = 0;
        int count = 0;
        for (auto &it : core)
        {
            if (it.second.first == K)
                count++;
        }
        while (!s.empty() && count != 0)
        {
            pair<int, int> p = *s.begin();
            s.erase(s.begin());
            k = max(k, p.second);
            if (core[p.first].first == K)
            {
                hvisitNode[p.first] = true;
                count--;
                core[p.first].second = k;
            }
            for (auto &edge : hyperNode.at(p.first))
            {
                if (visitEdgeTmp[edge])
                    continue;
                visitEdgeTmp[edge] = true;

                for (int i = 0; i < hyperEdge.at(edge).size(); i++)
                {
                    int v = hyperEdge.at(edge).at(i);
                    for (int j = 0; j < hyperEdge.at(edge).size(); j++)
                    {

                        int u = hyperEdge.at(edge).at(j);
                        if (v == u)
                            continue;
                        if (!hvisitNode[v] && v != p.first)
                            s.erase(make_pair(v, nbr[v].size()));
                        if (nbr[v].find(u) != nbr[v].end())
                            nbr[v][u]--;
                        if (nbr[v][u] == 0)
                            nbr[v].erase(u);
                        if (!hvisitNode[v] && v != p.first)
                            s.insert(make_pair(v, nbr[v].size()));
                    }
                }
            }
        }
    }
}

/**
 * @brief The degree of the hypernode on the path where the k-core is equal
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param core K-core value of hypernode
 * @param u Root hypernode
 * @param preEdge The path where the k-core is equal
 * @param cd The degree of the hypernode on the path where the k-core is equal
 */
void findHypergraphSubCore(const vector<vector<int>> &hyperEdge, const unordered_map<int, vector<int>> &hyperNode, const unordered_map<int, pair<int, int>> &core, int u,
                           unordered_map<int, vector<int>> &preEdge, unordered_map<int, int> &cd)
{
    unordered_map<int, bool> visitNode;
    queue<int> Q;
    int k = core.at(u).first;
    Q.push(u);
    visitNode[u] = true;
    vector<int> visitEdge(hyperEdge.size(), false);
    while (!Q.empty())
    {
        int v = Q.front();
        Q.pop();
        cd[v] = 0;
        for (auto &edge : hyperNode.at(v))
        {
            int minK = INT_MAX;
            for (auto &w : hyperEdge[edge])
                minK = min(minK, core.at(w).first);
            if (minK == k)
            {
                cd[v]++;
                preEdge[v].push_back(edge);
                if (visitEdge[edge])
                    continue;
                visitEdge[edge] = true;
                for (auto &w : hyperEdge[edge])
                {

                    if (minK == core.at(w).first && visitNode.find(w) == visitNode.end())
                    {
                        Q.push(w);
                        visitNode[w] = true;
                    }
                }
            }
        }
    }
}

/**
 * @brief Kh-core insertion of hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param cocore K-core value of hypernode
 * @param e The inserted hyperedge
 * @param index The inseted index
 */
void hypergraph_dynamic_insert(vector<vector<int>> &hyperEdge, unordered_map<int, vector<int>> &hyperNode, unordered_map<int, pair<int, int>> &cocore, const vector<int> &e, int index)
{
    int k = INT_MAX;
    int h = INT_MAX;
    bool flag = false;
    for (auto &it : e)
    {
        hyperEdge[index].push_back(it);
        hyperNode[it].push_back(index);
        if (cocore.find(it) != cocore.end() && cocore[it].first != 0)
        {
            k = min(k, cocore[it].first);
        }
        else
        {
            cocore[it].first = 1;
            cocore[it].second = 1;
            k = 1;
            h = 1;
            flag = true;
        }
    }
    vector<int> minkh;
    for (auto &it : e)
    {
        if (cocore[it].first == k)
        {
            h = min(h, cocore[it].second);
            minkh.push_back(it);
        }
    }
    bool is_k_constant = true;
    unordered_map<int, int> cd;
    if (!flag) 
    {
        unordered_map<int, vector<int>> preEdge;
        findHypergraphSubCore(hyperEdge, hyperNode, cocore, minkh[0], preEdge, cd);
        set<pair<int, int>, myCmp> mcd;
        unordered_map<int, int> deg;
        for (auto &node : cd)
        {
            if (cocore[node.first].first == k)
            {
                mcd.insert(make_pair(node.first, node.second));
                deg[node.first] = node.second;
            }
        }
        vector<bool> visitEdge(hyperEdge.size(), false);
        while (!mcd.empty() && (*mcd.begin()).second <= k)
        {
            pair<int, int> p = *mcd.begin();
            mcd.erase(mcd.begin());
            int v = p.first;
            for (auto &edge : preEdge[v])
            {
                if (visitEdge[edge])
                    continue;
                visitEdge[edge] = true;
                for (auto &node : hyperEdge[edge])
                {
                    if (deg.find(node) == deg.end() || deg.at(node) <= deg.at(v))
                        continue;
                    mcd.erase(make_pair(node, deg[node]));
                    deg[node]--;
                    mcd.insert(make_pair(node, deg[node]));
                }
            }
            deg.erase(v);
        }
        cd.clear();
        if (!mcd.empty())
            is_k_constant = false;
        while (!mcd.empty())
        {
            pair<int, int> p = *mcd.begin();
            cd.insert(p);
            mcd.erase(mcd.begin());
            cocore[p.first].first++;
        }
    }
    if (flag)
    {
        k = 1;
    }
    else
    {
        if (!is_k_constant)
            k++;
    }
    unordered_map<int, unordered_set<int>> nbr;
    if (cd.empty())
    {
        for (auto &it : minkh)
            nbr[it] = unordered_set<int>{};
    }
    else
    {
        for (auto &it : cd)
            nbr[it.first] = unordered_set<int>{};
    }
    auto minkhInEdge = [&cocore, &hyperEdge](int index) -> PII
    {
        int tmpk = INT_MAX, tmph = INT_MAX;
        for (auto &it : hyperEdge[index])
        {
            if (tmpk > cocore[it].first)
            {
                tmpk = cocore[it].first;
                tmph = cocore[it].second;
            }
            else if (tmpk == cocore[it].first)
            {
                tmph = min(tmph, cocore[it].second);
            }
        }
        return make_pair(tmpk, tmph);
    };
    auto computeMaxH = [&cocore](const unordered_set<int> &s) -> int
    {
        int maxH = 0;
        for (auto &it : s)
            maxH = max(maxH, cocore[it].second);
        vector<int> count(maxH + 1, 0);
        for (auto &it : s)
            count[cocore[it].second]++;
        for (int i = maxH - 1; i >= 0; i--)
            count[i] = count[i] + count[i + 1];
        int index = maxH;
        while (count[index] < index)
        {
            index--;
        }
        return index;
    };
    vector<PII> maxh; 
    for (auto &it : nbr)
    {
        for (auto &edge : hyperNode[it.first])
        {
            if (cocore[it.first].first == minkhInEdge(edge).first)
            {
                for (auto &node : hyperEdge[edge])
                {
                    it.second.insert(node);
                }
            }
        }
        it.second.erase(it.first);
        int tmp = computeMaxH(it.second);
        maxh.push_back(make_pair(it.first, tmp));
    }
    int h_LB = INT_MAX, h_UB = INT_MIN;
    for (int i = 0; i < maxh.size(); i++)
    {
        h_UB = max(h_UB, int(nbr[maxh[i].first].size()));
    }
    if (!is_k_constant)
    {
        for (int i = 0; i < maxh.size(); i++)
        {
            h_LB = min(h_LB, maxh[i].second);
        }
        h_LB = 0;
    }
    else
        h_LB = h;
    vector<bool> isDelete(hyperEdge.size(), false);

    unordered_map<int, bool> visitNode;
    for (auto &it : hyperNode)
    {
        if (cocore[it.first].first < k)
        {
            visitNode[it.first] = true;
            for (auto &edge : it.second)
                isDelete[edge] = true;
        }
        else if (cocore[it.first].first == k && cocore[it.first].second < h_LB)
        {
            visitNode[it.first] = true;
            for (auto &edge : it.second)
                isDelete[edge] = true;
        }
    }
    unordered_map<int, unordered_map<int, int>> hnbr;
    set<pair<int, int>, myCmp> s;
    for (auto &it : hyperNode)
    {
        if (visitNode[it.first])
            continue;
        for (auto &edge : it.second)
        {
            if (isDelete[edge])
                continue;
            for (auto &node : hyperEdge[edge])
            {
                hnbr[it.first][node]++;
            }
        }
        hnbr[it.first].erase(it.first);
        s.insert(make_pair(it.first, hnbr[it.first].size()));
    }
    h = h_LB;
    while (!s.empty())
    {
        pair<int, int> p = *s.begin();
        s.erase(s.begin());
        h = max(h, p.second);
        if (h > h_UB)
            break;
        if (cocore[p.first].first == k)
        {
            cocore[p.first].second = h;
        }
        visitNode[p.first] = true;
        for (auto &edge : hyperNode[p.first])
        {
            if (isDelete[edge])
                continue;
            isDelete[edge] = true;

            for (int i = 0; i < hyperEdge[edge].size(); i++)
            {
                int v = hyperEdge[edge][i];
                if (v == p.first)
                    continue;
                if (!visitNode[v])
                    s.erase(make_pair(v, hnbr[v].size()));
                for (int j = 0; j < hyperEdge[edge].size(); j++)
                {
                    int u = hyperEdge[edge][j];
                    if (v == u)
                        continue;
                    if (hnbr[v].find(u) != hnbr[v].end())
                        hnbr[v][u]--;
                    if (hnbr[v][u] == 0)
                        hnbr[v].erase(u);
                }
                if (!visitNode[v])
                    s.insert(make_pair(v, hnbr[v].size()));
            }
        }
        hnbr[p.first].clear();
    }
}

/**
 * @brief Kh-core erasing of hypergraph
 * 
 * @param hyperEdge Point set corresponding to hyperedge
 * @param hyperNode Edge set corresponding to hypernode
 * @param cocore Kh-core value of hypernode
 * @param index The erased index
 */
void hypergraph_dynamic_erase(vector<vector<int>> &hyperEdge, unordered_map<int, vector<int>> &hyperNode, unordered_map<int, pair<int, int>> &cocore, int index)
{
    int k = INT_MAX;
    int h = INT_MAX;
    vector<int> e(hyperEdge[index]);
    hyperEdge[index] = vector<int>();
    for (auto &it : e)
    {
        hyperNode[it].erase(find(hyperNode[it].begin(), hyperNode[it].end(), index));
        k = min(k, cocore[it].first);
    }
    vector<int> minkh;
    for (auto &it : e)
    {
        if (cocore[it].first == k)
        {
            h = min(h, cocore[it].second);
            minkh.push_back(it);
        }
    }
    bool is_k_constant = true;
    unordered_map<int, int> cd;
    unordered_map<int, vector<int>> preEdge;
    for (auto &it : minkh)
    {
        unordered_map<int, int> cdd;
        unordered_map<int, vector<int>> preEdgee;
        findHypergraphSubCore(hyperEdge, hyperNode, cocore, it, preEdgee, cdd);
        for (auto &t1 : cdd)
        {
            if (cd.find(t1.first) == cd.end())
                cd[t1.first] = t1.second;
        }
        for (auto &t2 : preEdgee)
        {
            if (preEdge.find(t2.first) == preEdge.end())
                preEdge[t2.first] = t2.second;
        }
    }
    set<pair<int, int>, myCmp> mcd;
    unordered_map<int, int> deg;
    for (auto &node : cd)
    {
        if (cocore[node.first].first == k)
        {
            mcd.insert(make_pair(node.first, node.second));
            deg[node.first] = node.second;
        }
    }
    vector<bool> visitEdge(hyperEdge.size(), false);
    cd.clear();
    while (!mcd.empty() && (*mcd.begin()).second < k)
    {
        pair<int, int> p = *mcd.begin();
        mcd.erase(mcd.begin());
        int v = p.first;
        cd[v] = 0;
        for (auto &edge : preEdge[v])
        {
            if (visitEdge[edge])
                continue;
            visitEdge[edge] = true;
            for (auto &node : hyperEdge[edge])
            {
                if (deg.find(node) == deg.end() || deg.at(node) <= deg.at(v))
                    continue;
                mcd.erase(make_pair(node, deg[node]));
                deg[node]--;
                mcd.insert(make_pair(node, deg[node]));
            }
        }
        deg.erase(v);
    }
    for (auto &it : cd)
    {
        is_k_constant = false;
        cocore[it.first].first--;
    }
    if (true)
    {
        unordered_map<int, unordered_set<int>> nbr;
        for (auto &it : minkh)
        {
            if (cocore[it].first == k)
            {
                nbr[it] = unordered_set<int>{};
            }
        }
        auto minkhInEdge = [&cocore, &hyperEdge](int index) -> PII
        {
            int tmpk = INT_MAX, tmph = INT_MAX;
            for (auto &it : hyperEdge[index])
            {
                if (tmpk > cocore[it].first)
                {
                    tmpk = cocore[it].first;
                    tmph = cocore[it].second;
                }
                else if (tmpk == cocore[it].first)
                {
                    tmph = min(tmph, cocore[it].second);
                }
            }
            return make_pair(tmpk, tmph);
        };
        auto computeMaxH = [&cocore](const unordered_set<int> &s) -> int
        {
            int maxH = 0;
            for (auto &it : s)
                maxH = max(maxH, cocore[it].second);
            vector<int> count(maxH + 1, 0);
            for (auto &it : s)
                count[cocore[it].second]++;
            for (int i = maxH - 1; i >= 0; i--)
                count[i] = count[i] + count[i + 1];
            int index = maxH;
            while (count[index] < index)
            {
                index--;
            }
            return index;
        };

        vector<PII> maxh;
        for (auto &it : nbr)
        {
            for (auto &edge : hyperNode[it.first])
            {
                if (cocore[it.first].first == minkhInEdge(edge).first)
                {
                    for (auto &node : hyperEdge[edge])
                    {
                        it.second.insert(node);
                    }
                }
            }
            it.second.erase(it.first);
            int tmp = computeMaxH(it.second);
            maxh.push_back(make_pair(it.first, tmp));
        }
        int h_LB = INT_MAX, h_UB = INT_MAX;
        for (int i = 0; i < maxh.size(); i++)
        {
            h_LB = min(h_LB, maxh[i].second);
            h_UB = min(h_UB, cocore[maxh[i].first].second);
        }
        h_LB = 0;
        vector<bool> isDelete(hyperEdge.size(), false);

        unordered_map<int, bool> visitNode;
        for (auto &it : hyperNode)
        {
            if (cocore[it.first].first < k)
            {
                visitNode[it.first] = true;
                for (auto &edge : it.second)
                    isDelete[edge] = true;
            }
            else if (cocore[it.first].first == k && cocore[it.first].second < h_LB)
            {
                visitNode[it.first] = true;
                for (auto &edge : it.second)
                    isDelete[edge] = true;
            }
        }
        unordered_map<int, unordered_map<int, int>> hnbr;
        set<pair<int, int>, myCmp> s;
        for (auto &it : hyperNode)
        {
            if (visitNode[it.first])
                continue;
            for (auto &edge : it.second)
            {
                if (isDelete[edge])
                    continue;
                for (auto &node : hyperEdge[edge])
                {
                    hnbr[it.first][node]++;
                }
            }
            hnbr[it.first].erase(it.first);
            s.insert(make_pair(it.first, hnbr[it.first].size()));
        }
        h = h_LB;
        while (!s.empty())
        {
            pair<int, int> p = *s.begin();
            s.erase(s.begin());
            h = max(h, p.second);
            if (h > h_UB)
            {
                break;
            }

            if (cocore[p.first].first == k)
            {
                cocore[p.first].second = h;
            }
            visitNode[p.first] = true;
            for (auto &edge : hyperNode[p.first])
            {
                if (isDelete[edge])
                    continue;
                isDelete[edge] = true;

                for (int i = 0; i < hyperEdge[edge].size(); i++)
                {
                    int v = hyperEdge[edge][i];
                    if (v == p.first)
                        continue;
                    if (!visitNode[v])
                        s.erase(make_pair(v, hnbr[v].size()));
                    for (int j = 0; j < hyperEdge[edge].size(); j++)
                    {
                        int u = hyperEdge[edge][j];
                        if (v == u)
                            continue;
                        if (hnbr[v].find(u) != hnbr[v].end())
                            hnbr[v][u]--;
                        if (hnbr[v][u] == 0)
                            hnbr[v].erase(u);
                    }
                    if (!visitNode[v])
                        s.insert(make_pair(v, hnbr[v].size()));
                }
            }
            hnbr[p.first].clear();
        }
    }

    if (!cd.empty())
    {
        k--;
        unordered_map<int, unordered_set<int>> nbr;
        for (auto &it : cd)
            nbr[it.first] = unordered_set<int>{};
        auto minkhInEdge = [&cocore, &hyperEdge](int index) -> PII
        {
            int tmpk = INT_MAX, tmph = INT_MAX;
            for (auto &it : hyperEdge[index])
            {
                if (tmpk > cocore[it].first)
                {
                    tmpk = cocore[it].first;
                    tmph = cocore[it].second;
                }
                else if (tmpk == cocore[it].first)
                {
                    tmph = min(tmph, cocore[it].second);
                }
            }
            return make_pair(tmpk, tmph);
        };
        auto computeMaxH = [&cocore](const unordered_set<int> &s) -> int
        {
            int maxH = 0;
            for (auto &it : s)
                maxH = max(maxH, cocore[it].second);
            vector<int> count(maxH + 1, 0);
            for (auto &it : s)
                count[cocore[it].second]++;
            for (int i = maxH - 1; i >= 0; i--)
                count[i] = count[i] + count[i + 1];
            int index = maxH;
            while (count[index] < index)
            {
                index--;
            }
            return index;
        };
        vector<PII> maxh;
        for (auto &it : nbr)
        {
            for (auto &edge : hyperNode[it.first])
            {
                if (cocore[it.first].first == minkhInEdge(edge).first)
                {
                    for (auto &node : hyperEdge[edge])
                    {
                        it.second.insert(node);
                    }
                }
            }
            it.second.erase(it.first);
            int tmp = computeMaxH(it.second);

            maxh.push_back(make_pair(it.first, tmp));
        }
        int h_LB = INT_MAX, h_UB = INT_MIN;
        for (int i = 0; i < maxh.size(); i++)
        {
            h_LB = min(h_LB, maxh[i].second);
            h_UB = max(h_UB, int(nbr[maxh[i].first].size()));
        }
        h_LB = 0;
        vector<bool> isDelete(hyperEdge.size(), false);

        unordered_map<int, bool> visitNode;
        for (auto &it : hyperNode)
        {
            if (cocore[it.first].first < k)
            {
                visitNode[it.first] = true;
                for (auto &edge : it.second)
                    isDelete[edge] = true;
            }
            else if (cocore[it.first].first == k && cocore[it.first].second < h_LB)
            {
                visitNode[it.first] = true;
                for (auto &edge : it.second)
                    isDelete[edge] = true;
            }
        }
        unordered_map<int, unordered_map<int, int>> hnbr;
        set<pair<int, int>, myCmp> s;
        for (auto &it : hyperNode)
        {
            if (visitNode[it.first])
                continue;
            for (auto &edge : it.second)
            {
                if (isDelete[edge])
                    continue;
                for (auto &node : hyperEdge[edge])
                {
                    hnbr[it.first][node]++;
                }
            }
            hnbr[it.first].erase(it.first);
            s.insert(make_pair(it.first, hnbr[it.first].size()));
        }
        h = h_LB;
        while (!s.empty())
        {
            pair<int, int> p = *s.begin();
            s.erase(s.begin());
            h = max(h, p.second);
            if (h > h_UB)
                break;
            if (cocore[p.first].first == k)
            {
                cocore[p.first].second = h;
            }
            visitNode[p.first] = true;
            for (auto &edge : hyperNode[p.first])
            {
                if (isDelete[edge])
                    continue;
                isDelete[edge] = true;

                for (int i = 0; i < hyperEdge[edge].size(); i++)
                {
                    int v = hyperEdge[edge][i];
                    if (v == p.first)
                        continue;
                    if (!visitNode[v])
                        s.erase(make_pair(v, hnbr[v].size()));
                    for (int j = 0; j < hyperEdge[edge].size(); j++)
                    {
                        int u = hyperEdge[edge][j];
                        if (v == u)
                            continue;
                        if (hnbr[v].find(u) != hnbr[v].end())
                        {
                            hnbr[v][u]--;
                            if (hnbr[v][u] == 0)
                                hnbr[v].erase(u);
                        }
                    }
                    if (!visitNode[v])
                        s.insert(make_pair(v, hnbr[v].size()));
                }
            }
            hnbr[p.first].clear();
        }
    }
}

/**
 * @brief Read kh-core from the file, reducing the time required for recalculation
 * 
 * @param filename Filename of kh-core
 * @param cocore Kh-core value of hypernode
 */
void readfile_khcore(const string &filename, unordered_map<int, PII> &cocore)
{
    string s = "./result/" + filename + "/" + filename + "-khcore.txt";
    ifstream fin(s);
    while (true)
    {
        string str;
        getline(fin, str);
        if (str == "")
            break;
        istringstream ss(str);
        int a, b, c;
        ss >> a >> b >> c;
        cocore[a] = make_pair(b, c);
    }
}
/**
 * @brief Calculate the time required for kh-core insertion and deletion of hypergraph
 * 
 * @return int 
 */
int main()
{
    //S_MaAn T_DBLP
    string file = "S_MiAc S_DrAb S_TrCl  S_WaTr  T_CoMH  T_ThAU  T_ThMS T_congress-bills T_DBLP S_MaAn";
    string filepath = "C++Projects/graphData/";
    istringstream ss(file);
    string str;
    while (ss >> str)
    {
        string filename = filepath + str;
        vector<vector<int>> hyperEdge;
        unordered_map<int, vector<int>> hyperNode;
        getGraph(filename, hyperEdge, hyperNode);
        cout << "****************************************************" << endl;
        cout << str << " has read!" << endl;
        cout << "edge is " << hyperEdge.size() << "  node is " << hyperNode.size() << endl;
        unordered_map<int, pair<int, int>> cocore;
        unordered_map<int, PII> fullcore;
        readfile_khcore(str, cocore);
        readfile_khcore(str, fullcore);
        cout << cocore.size() << " " << fullcore.size() << endl;
        cout << "khcoreDecomp is finished!" << endl;
        ofstream fout("./result/" + str + "/" + str + "-insertErase.txt");
        for (int len = 2; len <= 25; len++)
        {
            int num = 20;
            int j = 0;
            while (num > 0)
            {
                int index = -1;
                for (int i = j; i < hyperEdge.size(); i++)
                {
                    if (hyperEdge[i].size() == len)
                    {
                        index = i;
                        break;
                    }
                }
                if (index == -1)
                    break;
                cout << str << " len = " << len << " num = " << num-- << " index = " << index << endl;
                j = index + 1;
                vector<int> e(hyperEdge[index]);
                auto t1 = std::chrono::steady_clock::now();
                hypergraph_dynamic_erase(hyperEdge, hyperNode, cocore, index);
                auto t2 = std::chrono::steady_clock::now();
                hypergraph_dynamic_insert(hyperEdge, hyperNode, cocore, e, index);
                auto t3 = std::chrono::steady_clock::now();
                double dr_ns1 = std::chrono::duration<double, std::nano>(t2 - t1).count();
                double dr_ns2 = std::chrono::duration<double, std::nano>(t3 - t2).count();
                int mink = INT_MAX, minh = INT_MAX;
                for (auto &it : e)
                {
                    mink = min(mink, cocore[it].first);
                }
                for (auto &it : e)
                {
                    if (cocore[it].first == mink)
                        minh = min(minh, cocore[it].second);
                }
                fout << dr_ns1 << ' ' << dr_ns2 << ' ' << mink << ' ' << minh << ' ' << int(e.size()) << ' ' << index << ' ';
                for (auto &it : e)
                    fout << it << ' ';
                fout << endl;
            }
        }
        fout.close();
        for (auto &it : cocore)
        {
            if (it.second != fullcore[it.first])
            {
                cout << "error!" << endl;
                return 0;
            }
        }
        cout << "*************************************" << endl;
    }
}