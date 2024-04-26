#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <utility>
#include <vector>

using std::cerr;
using std::cout;
using std::endl;
using std::find_if;
using std::max;
using std::random_device;
using std::map;
using std::mt19937;
using std::ofstream;
using std::pair;
using std::set;
using std::stoi;
using std::string;
using std::to_string;
using std::uniform_int_distribution;
using std::vector;

auto main(int argc, char * argv[]) -> int
{
    if (argc != 4) {
        cerr << "Usage: " << argv[0] << " n-items max-item-weight max-weight\n";
        return EXIT_FAILURE;
    }

    vector<int> weights;
    vector<int> profits;
    int max_weight = stoi(argv[3]);

    random_device rd;
    mt19937 rand; // (rd());
    uniform_int_distribution dist{1, stoi(argv[2])};

    for (int i = 0, i_end = stoi(argv[1]) ; i < i_end ; ++i) {
        weights.push_back(dist(rand));
        profits.push_back(dist(rand));
    }

    {
        ofstream opb{"knapsack.opb"};
        opb << "min:";
        for (unsigned p = 0 ; p < profits.size() ; ++p)
            opb << " -" << profits[p] << " x" << p;
        opb << " ;\n";

        for (unsigned w = 0 ; w < weights.size() ; ++w)
            opb << -weights[w] << " x" << w << " ";
        opb << ">= -" << max_weight << " ;\n";
    }

    ofstream proof{"knapsack.veripb"};
    proof << "pseudo-Boolean proof version 2.0\n";
    int constraint_n = 1;

    int big_number = 0;
    for (auto & w : weights)
        big_number += w;
    for (auto & p : profits)
        big_number += p;

    vector<map<pair<int, int>, vector<int>>> states_by_layer(weights.size() + 1);
    vector<map<int, pair<string, int> > > wsums_by_layer(weights.size() + 1);
    vector<map<int, pair<string, int> > > psums_by_layer(weights.size() + 1);
    vector<map<pair<int, int>, string> > conjunctions_by_layer(weights.size() + 1);
    states_by_layer.at(0).emplace(pair<int, int>{0, 0}, vector<int>{});

    vector<unsigned> layer_start_nrs;
    unsigned total_states = 0, widest_layer = 0, total_transitions = 0;
    for (unsigned layer = 0 ; layer < weights.size() ; ++layer) {
        layer_start_nrs.push_back(constraint_n + 1);
        if (layer >= 2) {
            proof << "del range " << layer_start_nrs.at(layer - 2) << " " << layer_start_nrs.at(layer - 1) - 1 << "\n";
        }

        set<string> at_least_ones;

        for (auto & [state, how] : states_by_layer.at(layer)) {
            auto notake = how, take = how;
            notake.push_back(0);
            take.push_back(1);
            total_transitions += 2;

            states_by_layer.at(layer + 1).emplace(pair<int, int>{state.first, state.second}, notake);

            // first, let's try not taking the item
            auto wsum_notake = wsums_by_layer.at(layer + 1).find(state.first);
            if (wsum_notake == wsums_by_layer.at(layer + 1).end()) {
                // extension variable for partial sum of weights
                string n = "w" + to_string(layer + 1) + "_" + to_string(state.first);
                wsum_notake = wsums_by_layer.at(layer + 1).emplace(state.first, pair{n, constraint_n + 1}).first;

                proof << "red " << big_number << " ~" << n;
                for (unsigned l = 0 ; l <= layer ; ++l)
                    proof << " " << weights.at(l) << " x" << l;
                proof << " >= " << state.first << " ; " << n << " -> 0\n";
                proof << "red " << big_number << " " << n;
                for (unsigned l = 0 ; l <= layer ; ++l)
                    proof << " -" << weights.at(l) << " x" << l;
                proof << " >= " << (-state.first + 1) << " ; " << n << " -> 1\n";

                constraint_n += 2;
            }

            auto psum_notake = psums_by_layer.at(layer + 1).find(state.second);
            if (psum_notake == psums_by_layer.at(layer + 1).end()) {
                // extension variable for partial sum of profits
                string n = "p" + to_string(layer + 1) + "_" + to_string(state.second);
                psum_notake = psums_by_layer.at(layer + 1).emplace(state.second, pair{n, constraint_n + 1}).first;

                proof << "red " << big_number << " ~" << n;
                for (unsigned l = 0 ; l <= layer ; ++l)
                    proof << " -" << profits.at(l) << " x" << l;
                proof << " >= " << -state.second << " ; " << n << " -> 0\n";
                proof << "red " << big_number << " " << n;
                for (unsigned l = 0 ; l <= layer ; ++l)
                    proof << " " << profits.at(l) << " x" << l;
                proof << " >= " << state.second + 1 << " ; " << n << " -> 1\n";

                constraint_n += 2;
            }

            auto conj_notake = conjunctions_by_layer.at(layer + 1).find(pair{state.first, state.second});
            if (conj_notake == conjunctions_by_layer.at(layer + 1).end()) {
                // extension variable for conjunction of weights and profits
                string n = "c" + to_string(layer + 1) + "_" + to_string(state.first) + "_" + to_string(state.second);
                conj_notake = conjunctions_by_layer.at(layer + 1).emplace(pair{state.first, state.second}, n).first;

                proof << "red 2 ~" << n << " 1 " << wsum_notake->second.first << " 1 " << psum_notake->second.first << " >= 2 ; " << n << " -> 0\n";
                proof << "red 1 " << n << " 1 ~" << wsum_notake->second.first << " 1 ~" << psum_notake->second.first << " >= 1 ; " << n << " -> 1\n";
                constraint_n += 2;

                at_least_ones.insert(conj_notake->second);
            }

            // old state /\ ~x -> new state
            if (layer == 0) {
                proof << "rup 1 x" << layer << " 1 " << wsum_notake->second.first << " >= 1 ;\n";
                proof << "rup 1 x" << layer << " 1 " << psum_notake->second.first << " >= 1 ;\n";
                proof << "rup 1 x" << layer << " 1 " << conj_notake->second << " >= 1 ;\n";
                constraint_n += 3;
            }
            else {
                proof << "pol " << wsums_by_layer.at(layer).at(state.first).second << " " << wsum_notake->second.second + 1 << " + s\n";
                proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 x" << layer << " 1 " << wsum_notake->second.first << " >= 1 ;\n";
                proof << "pol " << psums_by_layer.at(layer).at(state.second).second << " " << psum_notake->second.second + 1 << " + s\n";
                proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 x" << layer << " 1 " << psum_notake->second.first << " >= 1 ;\n";
                proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 x" << layer << " 1 " << conj_notake->second << " >= 1 ;\n";
                constraint_n += 5;
            }

            // feasible to take the item?
            if (state.first + weights.at(layer) <= max_weight) {
                states_by_layer.at(layer + 1).emplace(pair<int, int>{state.first + weights.at(layer), state.second + profits.at(layer)}, take);

                auto wsum_take = wsums_by_layer.at(layer + 1).find(state.first + weights.at(layer));
                if (wsum_take == wsums_by_layer.at(layer + 1).end()) {
                    // extension variable for partial sum of weights
                    string n = "w" + to_string(layer + 1) + "_" + to_string(state.first + weights.at(layer));
                    wsum_take = wsums_by_layer.at(layer + 1).emplace(state.first + weights.at(layer), pair{n, constraint_n + 1}).first;

                    proof << "red " << big_number << " ~" << n;
                    for (unsigned l = 0 ; l <= layer ; ++l)
                        proof << " " << weights.at(l) << " x" << l;
                    proof << " >= " << (state.first + weights.at(layer)) << " ; " << n << " -> 0\n";
                    proof << "red " << big_number << " " << n;
                    for (unsigned l = 0 ; l <= layer ; ++l)
                        proof << " -" << weights.at(l) << " x" << l;
                    proof << " >= " << (-(state.first + weights.at(layer)) + 1) << " ; " << n << " -> 1\n";

                    constraint_n += 2;
                }

                auto psum_take = psums_by_layer.at(layer + 1).find(state.second + profits.at(layer));
                if (psum_take == psums_by_layer.at(layer + 1).end()) {
                    // extension variable for partial sum of profits
                    string n = "p" + to_string(layer + 1) + "_" + to_string(state.second + profits.at(layer));
                    psum_take = psums_by_layer.at(layer + 1).emplace(state.second + profits.at(layer), pair{n, constraint_n + 1}).first;

                    proof << "red " << big_number << " ~" << n;
                    for (unsigned l = 0 ; l <= layer ; ++l)
                        proof << " -" << profits.at(l) << " x" << l;
                    proof << " >= " << -(state.second + profits.at(layer)) << " ; " << n << " -> 0\n";
                    proof << "red " << big_number << " " << n;
                    for (unsigned l = 0 ; l <= layer ; ++l)
                        proof << " " << profits.at(l) << " x" << l;
                    proof << " >= " << (state.second + profits.at(layer)) + 1 << " ; " << n << " -> 1\n";

                    constraint_n += 2;
                }

                auto conj_take = conjunctions_by_layer.at(layer + 1).find(pair{state.first + weights.at(layer), state.second + profits.at(layer)});
                if (conj_take == conjunctions_by_layer.at(layer + 1).end()) {
                    // extension variable for conjunction of weights and profits
                    string n = "c" + to_string(layer + 1) + "_" + to_string(state.first + weights.at(layer)) + "_" + to_string(state.second + profits.at(layer));
                    conj_take = conjunctions_by_layer.at(layer + 1).emplace(pair{state.first + weights.at(layer), state.second + profits.at(layer)}, n).first;

                    proof << "red 2 ~" << n << " 1 " << wsum_take->second.first << " 1 " << psum_take->second.first << " >= 2 ; " << n << " -> 0\n";
                    proof << "red 1 " << n << " 1 ~" << wsum_take->second.first << " 1 ~" << psum_take->second.first << " >= 1 ; " << n << " -> 1\n";
                    constraint_n += 2;
                }

                // state /\ x -> new state
                if (layer == 0) {
                    proof << "rup 1 ~x" << layer << " 1 " << wsum_take->second.first << " >= 1 ;\n";
                    proof << "rup 1 ~x" << layer << " 1 " << psum_take->second.first << " >= 1 ;\n";
                    proof << "rup 1 ~x" << layer << " 1 " << conj_take->second << " >= 1 ;\n";
                    constraint_n += 3;
                }
                else {
                    proof << "pol " << wsums_by_layer.at(layer).at(state.first).second << " " << wsum_take->second.second + 1 << " + s\n";
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 ~x" << layer << " 1 " << wsum_take->second.first << " >= 1 ;\n";
                    proof << "pol " << psums_by_layer.at(layer).at(state.second).second << " " << psum_take->second.second + 1 << " + s\n";
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 ~x" << layer << " 1 " << psum_take->second.first << " >= 1 ;\n";
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 ~x" << layer << " 1 " << conj_take->second << " >= 1 ;\n";
                    constraint_n += 5;
                }

                at_least_ones.insert(conj_take->second);

                if (layer != 0) {
                    // old state -> one of the new states
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 " << conj_notake->second << " 1 " << conj_take->second << " >= 1 ;\n";
                    constraint_n += 1;
                }
            }
            else {
                // old state -> not x
                if (layer == 0) {
                    proof << "rup 1 ~x" << layer << " >= 1 ;\n";
                    ++constraint_n;
                }
                else {
                    proof << "pol 1 " << wsums_by_layer.at(layer).at(state.first).second << " + s\n";
                    proof << "rup 1 ~" << wsums_by_layer.at(layer).at(state.first).first << " 1 ~x" << layer << " >= 1 ;\n";
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 ~x" << layer << " >= 1 ;\n";

                    // old state -> new state
                    proof << "rup 1 ~" << conjunctions_by_layer.at(layer).at(state) << " 1 " << conj_notake->second << " >= 1 ;\n";

                    constraint_n += 4;
                }
            }
        }

        // have to take one of the states at this level
        proof << "rup";
        for (auto & al1 : at_least_ones)
            proof << " 1 " << al1;
        proof << " >= 1 ;\n";
        constraint_n += 1;

        // try to find any dominating states, and cancel them
        for (auto state = states_by_layer.at(layer + 1).begin(),
                state_end = states_by_layer.at(layer + 1).end() ; state != state_end ; ) {
            auto better = find_if(states_by_layer.at(layer + 1).begin(), states_by_layer.at(layer + 1).end(),
                    [&] (const pair<pair<int, int>, vector<int> > & other) {
                        return other.first != state->first && other.first.first <= state->first.first && other.first.second >= state->first.second;
                    });
            if (better != state_end) {
                // worse state -> better state
                proof << "pol " << wsums_by_layer.at(layer + 1).at(state->first.first).second << " " << wsums_by_layer.at(layer + 1).at(better->first.first).second + 1 << " + s ;\n";
                proof << "rup 1 ~" << wsums_by_layer.at(layer + 1).at(state->first.first).first << " 1 " << wsums_by_layer.at(layer + 1).at(better->first.first).first << " >= 1 ;\n";
                proof << "pol " << psums_by_layer.at(layer + 1).at(state->first.second).second << " " << psums_by_layer.at(layer + 1).at(better->first.second).second + 1 << " + s ;\n";
                proof << "rup 1 ~" << psums_by_layer.at(layer + 1).at(state->first.second).first << " 1 " << psums_by_layer.at(layer + 1).at(better->first.second).first << " >= 1 ;\n";
                proof << "rup 1 ~" << conjunctions_by_layer.at(layer + 1).at(state->first) << " 1 " << conjunctions_by_layer.at(layer + 1).at(better->first) << " >= 1 ;\n";
                constraint_n += 5;
                states_by_layer.at(layer + 1).erase(state++);
            }
            else
                ++state;
        }

        total_states += states_by_layer.at(layer + 1).size();
        widest_layer = max<unsigned>(widest_layer, states_by_layer.at(layer + 1).size());
    }

    if (states_by_layer.at(weights.size()).empty()) {
        proof << "output NONE\n";
        proof << "conclusion UNSATISFIABLE\n";
        proof << "end pseudo-Boolean proof\n";
    }
    else {
        auto & final_psums = psums_by_layer.at(weights.size());
        set<int> final_profits;
        for (auto & [p, _] : final_psums)
            final_profits.insert(p);

        // establish that profit <= x -> profit <= y for each x < y that shows up on the final layer
        for (auto x = final_profits.begin(), next_x = next(x), x_end = final_profits.end() ; x != x_end && next_x != x_end ; ++x, ++next_x) {
            proof << "pol " << final_psums.at(*x).second << " " << final_psums.at(*next_x).second + 1 << " + s\n";
            proof << "rup 1 ~" << final_psums.at(*x).first << " 1 " << final_psums.at(*next_x).first << " >= 1 ;\n";
            constraint_n += 2;
        }

        // profit <= best profit on final layer
        proof << "rup 1 " << final_psums.at(*final_profits.rbegin()).first << " >= 1 ;\n";
        ++constraint_n;
        int bounds_line = final_psums.at(*final_profits.rbegin()).second;

        for (auto & [state, how] : states_by_layer.at(weights.size())) {
            if (state.second == *final_profits.rbegin()) {
                // log solution
                proof << "soli";
                for (unsigned w = 0 ; w < how.size() ; ++w)
                    proof << " " << (how.at(w) ? "x" : "~x") << w;
                proof << '\n';
                proof << "pol -1 " << bounds_line << " +\n";
                constraint_n += 2;

                break;
            }
        }

        // need to explicitly derive the lower bound
        proof << "rup";
        for (unsigned p = 0 ; p < profits.size() ; ++p)
            proof << " -" << profits[p] << " x" << p;
        proof << " >= " << -*final_profits.rbegin() << " ;\n";
        ++constraint_n;

        proof << "output NONE\n";
        proof << "conclusion BOUNDS " << -*final_profits.rbegin() << " " << -*final_profits.rbegin() << "\n";
        proof << "end pseudo-Boolean proof\n";
    }

    cout << widest_layer << " " << total_states << " " << total_transitions << "\n";

    return EXIT_SUCCESS;
}
