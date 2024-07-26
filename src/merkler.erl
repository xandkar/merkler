-module(merkler).

-export([
    tree/1,
    root/1,
    proof/2,
    proof_is_valid/2
]).

-export_type([tree/0, level/0]).

%% API ========================================================================

-type tree() :: [level()].
-type level() :: [binary()].

-spec tree([binary()]) -> tree().
tree([_|_]=Leaves0) ->
    N = length(Leaves0),
    Leaves1 = Leaves0 ++ lists:duplicate(max(2, next_pow_of_2(N)) - N, <<>>),
    Leaves2 = [hash(L, <<>>) || L <- Leaves1],
    lists:reverse([Leaves2 | levels_up(Leaves2)]).

-spec root(tree()) -> binary().
root([[Root] | _]) -> Root.

%% Minimal subtree which converges on the same root as original.
-spec proof(pos_integer(), tree()) -> tree().
proof(LeafPos, Tree) ->
    {_, Proof} =
        lists:foldl(
            fun(Level, {Pos, Proof}) ->
                    Parent = ceil(Pos / 2),
                    ChildLeft = (Parent * 2) - 1,
                    Siblings = lists:sublist(Level, ChildLeft, 2),
                    {Parent, [Siblings | Proof]}
            end,
            {LeafPos, []},
            lists:reverse(Tree)
        ),
    Proof.

%% Check that the subtree converges on the same root as given.
-spec proof_is_valid(tree(), binary()) -> boolean().
proof_is_valid([[<<Root/binary>>] | _]=Proof, <<Root/binary>>) ->
    is_convergent(lists:reverse(Proof));
proof_is_valid([[<<_/binary>>] | _], <<_/binary>>) ->
    false.

%% Internal ===================================================================

%% XXX Expecting [leaves, .., [root]] order, i.e. reversed tree.
-spec is_convergent(tree()) -> boolean().
is_convergent([[_Root]]) ->
    true;
is_convergent([[Sibling1, Sibling2], [_|_]=LevelUp | LevelsUp]) ->
    lists:member(hash(Sibling1, Sibling2), LevelUp)
    andalso
    is_convergent([LevelUp | LevelsUp]).

-spec levels_up([binary()]) -> tree().
levels_up([_|_]=Leaves) ->
    case level_up(Leaves) of
        [_]=L -> [L];
        [_|_]=L -> [L | levels_up(L)]
    end.

-spec level_up([binary()]) -> level().
level_up([]) ->
    [];
level_up([B1, B2 | Bins]) ->
    [hash(B1, B2) | level_up(Bins)].

-spec hash(binary(), binary()) -> binary().
hash(A, B) ->
    crypto:hash(sha256, [A, B]).

-spec next_pow_of_2(pos_integer()) -> pos_integer().
next_pow_of_2(N) when N > 0 ->
    floor(math:pow(2, ceil(math:log(N) / math:log(2)))).

%% Tests ======================================================================

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

next_pow_of_2_test_()->
    [
        [
            ?_assertEqual(1, next_pow_of_2(1)),
            ?_assertEqual(2, next_pow_of_2(2)),
            ?_assertEqual(4, next_pow_of_2(3)),
            ?_assertEqual(4, next_pow_of_2(4)),
            ?_assertEqual(8, next_pow_of_2(5)),
            ?_assertEqual(8, next_pow_of_2(6)),
            ?_assertEqual(8, next_pow_of_2(7)),
            ?_assertEqual(8, next_pow_of_2(8)),
            ?_assertEqual(16, next_pow_of_2(9)),
            ?_assertEqual(16, next_pow_of_2(10)),
            ?_assertEqual(16, next_pow_of_2(11)),
            ?_assertEqual(16, next_pow_of_2(12)),
            ?_assertEqual(16, next_pow_of_2(13)),
            ?_assertEqual(16, next_pow_of_2(14)),
            ?_assertEqual(16, next_pow_of_2(15)),
            ?_assertEqual(16, next_pow_of_2(16)),
            ?_assertEqual(32, next_pow_of_2(17))
        |
            [?_assertEqual(Target, next_pow_of_2(N)) || N <- Range]
        ]
    ||
        {Target, Range} <-
            [
                {X, lists:seq(floor(X / 2) + 1, X)}
            ||
                X <- [floor(math:pow(2, X)) || X <- lists:seq(5, 10)]
            ]
    ].

merkle_test_() ->
    A = <<"a">>,
    B = <<"b">>,
    C = <<"c">>,
    D = <<"d">>,
    E = <<"e">>,
    F = <<"f">>,
    H = fun hash/2,
    H__ = H(<<>>, <<>>),
    H_A = H(A, <<>>),
    H_B = H(B, <<>>),
    H_C = H(C, <<>>),
    H_D = H(D, <<>>),
    H_E = H(E, <<>>),
    H_F = H(F, <<>>),
    H_AB = H(H_A, H_B),
    H_CD = H(H_C, H_D),
    H_EF = H(H_E, H_F),
    H_ABCD = H(H_AB, H_CD),
    Tests =
        % A
        (fun() ->
            H_A_ = H(H_A, H__),
            L0 = [A],
            L1 = [H_A, H__],
            L2 = [H_A_],
            R = H_A_,
            T = [L2, L1],
            [
                ?_assertEqual(L2, level_up(L1)),
                ?_assertEqual([L2], levels_up(L1)),
                ?_assertEqual(T, tree(L0)),
                ?_assertEqual(R, root(T))
            ]
        end)()
        ++
        % AB
        (fun() ->
            L0 = [A, B],
            L1 = [H_A, H_B],
            L2 = [H_AB],
            R = H_AB,
            T = [L2, L1],
            [
                ?_assertEqual(L2, level_up(L1)),
                ?_assertEqual(T, tree(L0)),
                ?_assertEqual(R, root(T))
            ]
        end)()
        ++
        % ABC
        (fun() ->
            H_C_ = H(H_C, H__),
            H_ABC_ = H(H_AB, H_C_),
            L0 = [A, B, C],
            L1 = [H_A, H_B, H_C, H__],
            L2 = [H_AB, H_C_],
            L3 = [H_ABC_],
            R = H_ABC_,
            T = [L3, L2, L1],
            [
                ?_assertEqual(L2, level_up(L1)),
                ?_assertEqual(L3, level_up(L2)),
                ?_assertEqual(T, tree(L0)),
                ?_assertEqual(R, root(T))
            ]
        end)()
        ++
        % ABCD
        (fun() ->
            L0 = [A, B, C, D],
            L1 = [H_A, H_B, H_C, H_D],
            L2 = [H_AB, H_CD],
            L3 = [H_ABCD],
            R = H_ABCD,
            T = [L3, L2, L1],
            [
                ?_assertEqual(L2, level_up(L1)),
                ?_assertEqual(L3, level_up(L2)),
                ?_assertEqual(T, tree(L0)),
                ?_assertEqual(R, root(T))
            ]
        end)()
        ++
        % ABCDEF
        (fun() ->
            H___ = H(H__, H__),
            H_EF__ = H(H_EF, H___),
            H_ABCDEF__ = H(H_ABCD, H_EF__),
            L0 = [A, B, C, D, E, F],
            L1 = [H_A, H_B, H_C, H_D, H_E, H_F, H__, H__],
            L2 = [H_AB, H_CD, H_EF, H___],
            L3 = [H_ABCD, H_EF__],
            L4 = [H_ABCDEF__],
            R = H_ABCDEF__,
            T = [L4, L3, L2, L1],

            P1 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_AB, H_CD], [H_A, H_B]],
            P2 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_AB, H_CD], [H_A, H_B]],

            P3 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_AB, H_CD], [H_C, H_D]],
            P4 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_AB, H_CD], [H_C, H_D]],

            P5 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_EF, H___], [H_E, H_F]],
            P6 = [[H_ABCDEF__], [H_ABCD, H_EF__], [H_EF, H___], [H_E, H_F]],

            P6B = [[H_ABCDEF__], [H_ABCD, <<1>>], [H_EF, H___], [H_E, H_F]],

            [
                ?_assertEqual(L2, level_up(L1)),
                ?_assertEqual(L3, level_up(L2)),
                ?_assertEqual(L4, level_up(L3)),
                ?_assertEqual(T, tree(L0)),

                ?_assertEqual(P1, proof(1, T)),
                ?_assertEqual(P2, proof(2, T)),
                ?_assertEqual(P3, proof(3, T)),
                ?_assertEqual(P4, proof(4, T)),
                ?_assertEqual(P5, proof(5, T)),
                ?_assertEqual(P6, proof(6, T)),

                ?_assert(proof_is_valid(P1, R)),
                ?_assertNot(proof_is_valid(P1, <<0, R/binary>>)),
                ?_assert(proof_is_valid(P2, R)),
                ?_assert(proof_is_valid(P3, R)),
                ?_assert(proof_is_valid(P4, R)),
                ?_assert(proof_is_valid(P5, R)),
                ?_assert(proof_is_valid(P6, R)),
                ?_assertNot(proof_is_valid(P6B, R))
            ]
        end)()
        ++
        % Now let's try a big one:
        (fun () ->
            Data = crypto:strong_rand_bytes(64 * 1024),
            Chunks = chunk(Data, 32),
            N = length(Chunks),
            T = tree(Chunks),
            TreeHeight = length(T),
            [
                {
                    lists:flatten(io_lib:format(
                        "Construct and validate proof for "
                        "leaf#~p of ~p in tree of height ~p.",
                        [I, N, TreeHeight]
                    )),
                    ?_assert(proof_is_valid(proof(I, T), root(T)))
                }
            ||
                I <- lists:seq(1, N)
            ]
        end)(),
    {inparallel, Tests}.

-spec chunk(binary(), pos_integer()) -> [binary()].
chunk(<<Data0/binary>>, ChunkSize) when ChunkSize > 0 ->
    case Data0 of
        <<>> ->
            [];
        <<Chunk:ChunkSize/binary, Data1/binary>> ->
            [Chunk | chunk(Data1, ChunkSize)];
        <<Chunk/binary>> ->
            [Chunk]
    end.

-endif.
