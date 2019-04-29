#!/usr/bin/env pypy
# -*- coding: utf-8 -*-

from __future__ import print_function
import re, sys, time
from itertools import count
from collections import OrderedDict, namedtuple

###############################################################################
# Piece-Square tables. Tune these to change sunfish's behaviour
###############################################################################

piece = { 'P': 100, 'N': 280, 'B': 320, 'R': 479, 'Q': 929, 'K': 60000 }
pst = {
    'P': (   0,   0,   0,   0,   0,   0,   0,   0,
            78,  83,  86,  73, 102,  82,  85,  90,
             7,  29,  21,  44,  40,  31,  44,   7,
           -17,  16,  -2,  15,  14,   0,  15, -13,
           -26,   3,  10,   9,   6,   1,   0, -23,
           -22,   9,   5, -11, -10,  -2,   3, -19,
           -31,   8,  -7, -37, -36, -14,   3, -31,
             0,   0,   0,   0,   0,   0,   0,   0),
    'N': ( -66, -53, -75, -75, -10, -55, -58, -70,
            -3,  -6, 100, -36,   4,  62,  -4, -14,
            10,  67,   1,  74,  73,  27,  62,  -2,
            24,  24,  45,  37,  33,  41,  25,  17,
            -1,   5,  31,  21,  22,  35,   2,   0,
           -18,  10,  13,  22,  18,  15,  11, -14,
           -23, -15,   2,   0,   2,   0, -23, -20,
           -74, -23, -26, -24, -19, -35, -22, -69),
    'B': ( -59, -78, -82, -76, -23,-107, -37, -50,
           -11,  20,  35, -42, -39,  31,   2, -22,
            -9,  39, -32,  41,  52, -10,  28, -14,
            25,  17,  20,  34,  26,  25,  15,  10,
            13,  10,  17,  23,  17,  16,   0,   7,
            14,  25,  24,  15,   8,  25,  20,  15,
            19,  20,  11,   6,   7,   6,  20,  16,
            -7,   2, -15, -12, -14, -15, -10, -10),
    'R': (  35,  29,  33,   4,  37,  33,  56,  50,
            55,  29,  56,  67,  55,  62,  34,  60,
            19,  35,  28,  33,  45,  27,  25,  15,
             0,   5,  16,  13,  18,  -4,  -9,  -6,
           -28, -35, -16, -21, -13, -29, -46, -30,
           -42, -28, -42, -25, -25, -35, -26, -46,
           -53, -38, -31, -26, -29, -43, -44, -53,
           -30, -24, -18,   5,  -2, -18, -31, -32),
    'Q': (   6,   1,  -8,-104,  69,  24,  88,  26,
            14,  32,  60, -10,  20,  76,  57,  24,
            -2,  43,  32,  60,  72,  63,  43,   2,
             1, -16,  22,  17,  25,  20, -13,  -6,
           -14, -15,  -2,  -5,  -1, -10, -20, -22,
           -30,  -6, -13, -11, -16, -11, -16, -27,
           -36, -18,   0, -19, -15, -15, -21, -38,
           -39, -30, -31, -13, -31, -36, -34, -42),
    'K': (   4,  54,  47, -99, -99,  60,  83, -62,
           -32,  10,  55,  56,  56,  55,  10,   3,
           -62,  12, -57,  44, -67,  28,  37, -31,
           -55,  50,  11,  -4, -19,  13,   0, -49,
           -55, -43, -52, -28, -51, -47,  -8, -50,
           -47, -42, -43, -79, -64, -32, -29, -32,
            -4,   3, -14, -50, -57, -18,  13,   4,
            17,  30,  -3, -14,   6,  -1,  40,  18),
}
# Pad tables and join piece and pst dictionaries
for k, table in pst.items():
    padrow = lambda row: (0,) + tuple(x+piece[k] for x in row) + (0,)
    pst[k] = sum((padrow(table[i*8:i*8+8]) for i in range(8)), ())
    pst[k] = (0,)*20 + pst[k] + (0,)*20

###############################################################################
# Global constants
###############################################################################

# Our board is represented as a 120 character string. The padding allows for
# fast detection of moves that don't stay within the board.
A1, H1, A8, H8 = 91, 98, 21, 28


# Mate value must be greater than 8*queen + 2*(rook+knight+bishop)
# King value is set to twice this value such that if the opponent is
# 8 queens up, but we got the king, we still exceed MATE_VALUE.
# When a MATE is detected, we'll set the score to MATE_UPPER - plies to get there
# E.g. Mate in 3 will be MATE_UPPER - 6
MATE_LOWER = piece['K'] - 10*piece['Q']
MATE_UPPER = piece['K'] + 10*piece['Q']

# The table size is the maximum number of elements in the transposition table.
TABLE_SIZE = 1e8

# Constants for tuning search
QS_LIMIT = 150
EVAL_ROUGHNESS = 20


###############################################################################
# Chess logic
###############################################################################

class Piece(object):

    def __init__(self, piece_type, position):
        """
        representation of a piece on the board. Does not know about any other pieces on the board.
        """
        N, E, S, W = -10, 1, 10, -1
        move_map = {
            'P': (N, N+N, N+W, N+E),
            'N': (N+N+E, E+N+E, E+S+E, S+S+E, S+S+W, W+S+W, W+N+W, N+N+W),
            'B': (N+E, S+E, S+W, N+W),
            'R': (N, E, S, W),
            'Q': (N, E, S, W, N+E, S+E, S+W, N+W),
            'K': (N, E, S, W, N+E, S+E, S+W, N+W)
        }
        self.allowed_moves = move_map[piece_type]
        self.position = position
        self.piece_type = piece_type

    def get_allowed_moves(self):
        """
        Iterates over list of naive allowed moves without taking board position or other pieces into account
        """
        for move in self.allowed_moves:
            yield move

    def get_position(self):
        return self.position

    def is_pawn(self):
        return self.piece_type == 'P'

    def is_king(self):
        return self.piece_type == 'K'

    def is_knight(self):
        return self.piece_type == 'N'


class BoardSquare(object):

    def __init__(self, type, position):
        self.type = type
        self.position = position

    def is_friendly_piece(self):
        return self.type.isupper()

    def is_opponent_piece(self):
        return self.type.islower()

    def is_on_board(self):
        return not self.type.isspace()

    def is_empty(self):
        return self.type == '.'

    def get_position(self):
        return self.position

    def get_type(self):
        return self.type

    def to_piece(self):
        return Piece(self.type, self.position)

class Board(object):

    def __init__(self, initial_state=None):
        if initial_state is None:
            # TODO: explore replacing state with array of BoardSquares
            self.state = (
                '         \n'  #   0 -  9
                '         \n'  #  10 - 19
                ' rnbqkbnr\n'  #  20 - 29
                ' pppppppp\n'  #  30 - 39
                ' ........\n'  #  40 - 49
                ' ........\n'  #  50 - 59
                ' ........\n'  #  60 - 69
                ' ........\n'  #  70 - 79
                ' PPPPPPPP\n'  #  80 - 89
                ' RNBQKBNR\n'  #  90 - 99
                '         \n'  # 100 -109
                '         \n'  # 110 -119
            )
        else:
            self.state = initial_state

    def get_pieces(self):
        for position, square in enumerate(self.state):
            square = BoardSquare(square, position)
            if square.is_friendly_piece():
                yield square.to_piece()

    def get_square(self, index):
        return BoardSquare(self.state[index], index)

    def rotate(self):
        rotated_state=self.state[::-1].swapcase()
        return Board(initial_state=rotated_state)

    def put_square_at_position(self, square, position):
        new_state = self.state[:position] + square.get_type() + self.state[position+1:]
        self.state = new_state

    def copy(self):
        return Board(initial_state=str(self.state))


CastlingRights = namedtuple('CastlingRights', ['queen_side', 'king_side'])

N, E, S, W = -10, 1, 10, -1

class GameState(object):

    def __init__(self, board, score, castling_rights, opponent_castling_rights, en_passant, king_passant):
        """
        A state of a chess game
        board -- a 120 char representation of the board
        score -- the board evaluation
        wc -- the castling rights, [west/queen side, east/king side]
        bc -- the opponent castling rights, [west/king side, east/queen side]
        ep - the en passant square
        kp - the king passant square
        """
        self.board = board
        self.score = score
        self.castling_rights = castling_rights
        self.opponent_castling_rights = opponent_castling_rights
        self.en_passant = en_passant
        self.king_passant = king_passant

    def gen_moves(self):
        legal_moves = []
        for piece in self.board.get_pieces():
            for move in piece.get_allowed_moves():
                # now that we know which ways the piece can theoretically move, lets see how they work on the board
                legal_moves += self.get_legal_moves(move, piece)
        return legal_moves

    def get_legal_moves(self, move, piece):
        initial_position = piece.get_position()
        for current_position in count(initial_position+move, move):
            # now we are moving over the board, one movement length at a time. Peices that can only move a certain distance are covered by break statement at bottom
            square = self.board.get_square(current_position)
            if not square.is_on_board() or square.is_friendly_piece():
                # Stay inside the board, and off friendly pieces
                break
            if piece.is_pawn():
                if move in (N, N+N) and square.is_opponent_piece():
                    # can't attack in while moving with pawn
                    break
                if move == N+N:
                    if initial_position < A1+N or not self.board.get_square(initial_position+N).is_empty():
                        # can't double move except in starting position, and can't double move over obstacle
                        break
                if move in (N+W, N+E):
                    if square.is_empty() and current_position not in (self.en_passant, self.king_passant):
                        # can't move diagonal into an empty square unless en passant
                        break
            # Move it
            yield (initial_position, current_position)

            if (piece.is_pawn() or piece.is_king() or piece.is_knight() or square.is_opponent_piece()):
                # Stop crawlers from sliding, and sliding after captures
                break
            # Castling, by sliding the rook next to the king
            if initial_position == A1 and self.castling_rights[0]:
                target_position = self.board.get_square(current_position+E)
                if target_position.is_friendly_piece() and target_position.to_piece().is_king():
                    yield (current_position+E, current_position+W)
            if initial_position == H1 and self.castling_rights[1]:
                target_position = self.board.get_square(current_position+W)
                if target_position.is_friendly_piece() and target_position.to_piece().is_king():
                    yield (current_position+W, current_position+E)

    def rotate(self):
        ''' Rotates the board, preserving enpassant '''
        self.board.rotate()
        return GameState(
                          board=self.board.rotate(),
                          score=-self.score,
                          castling_rights=self.opponent_castling_rights,
                          opponent_castling_rights=self.castling_rights,
                          en_passant=(119-self.en_passant if self.en_passant else 0),
                          king_passant=(119-self.king_passant if self.king_passant else 0)
                         )

    def nullmove(self):
        ''' Like rotate, but clears ep and kp '''
        self.board.rotate()
        return GameState(
                          board=self.board.rotate(),
                          score=-self.score,
                          castling_rights=self.opponent_castling_rights,
                          opponent_castling_rights=self.castling_rights,
                          en_passant=0,
                          king_passant=0
                         )

    def move(self, move):
        """
        Returns a copy of the gamestate, ready for opponents play, after making the move specified in the parameter.
        """
        initial_position, end_position = move
        start_square, end_square = self.board.get_square(initial_position), self.board.get_square(end_position)
        # Copy variables and reset ep and kp
        board = self.board.copy()

        score = self.score + self.value(move)
        # Actual move
        board.put_square_at_position(square=start_square, position=end_position)
        board.put_square_at_position(square=BoardSquare(type='.', position=initial_position), position=initial_position)
        # Castling rights, we move the rook or capture the opponent's
        castling_rights = self.castling_rights
        opponent_castling_rights = self.opponent_castling_rights
        en_passant = self.en_passant
        king_passant = self.king_passant
        if start_square.get_position() == A1:
            castling_rights = (False, self.castling_rights[1])
        if start_square.get_position() == H1:
            castling_rights = (self.castling_rights[0], False)
        if end_square.get_position() == A8:
            opponent_castling_rights = (self.opponent_castling_rights[0], False)
        if end_square.get_position() == H8:
            opponent_castling_rights = (False, self.opponent_castling_rights[1])

        your_piece = start_square.to_piece()

        if your_piece.is_king():
            # if you moved the king always lose castling rights
            castling_rights = (False, False)
            if abs(end_square.get_position()-start_square.get_position()) == 2:
                # now handle case where you actually just castled
                kp = (start_square.get_position()+end_square.get_position())//2
                if end_square.get_position() < start_square.get_position():
                    board.put_square_at_position(square=BoardSquare(type='.', position=A1), position=A1)
                else:
                    board.put_square_at_position(square=BoardSquare(type='.', position=H1), position=H1)
                board.put_square_at_position(square=BoardSquare(type='R', position=kp), position=kp)

        if your_piece.is_pawn():
            if A8 <= end_square.get_position() <= H8:
                # always promote to queen
                board.put_square_at_position(square=BoardSquare(type='Q', position=end_position), position=end_position)
            if end_position - initial_position == 2*N:
                # update en passant square if you do a double move
                en_passant = initial_position + N
            if end_position - initial_position in (N+W, N+E) and end_square.is_empty():
                # if you just captured in passant, remove the captured peice
                board.put_square_at_position(square=BoardSquare(type='.', position=end_position+S), position=end_position+S)
        # We rotate the returned position, so it's ready for the next player
        game_state_after_move = GameState(
                                          board=board,
                                          score=score,
                                          castling_rights=castling_rights,
                                          opponent_castling_rights=opponent_castling_rights,
                                          en_passant=en_passant,
                                          king_passant=king_passant
                                        )
        return game_state_after_move.rotate()

    def value(self, move):
        """
        Determines the worth of the specified move
        """
        initial_position, end_position = move
        start_square, end_square = self.board.get_square(initial_position), self.board.get_square(end_position)
        # Actual move - pst is the array of points per piece type per position
        score = pst[start_square.get_type()][end_position] - pst[start_square.get_type()][initial_position]
        # Capture
        if end_square.is_opponent_piece():
            score += pst[end_square.get_type().upper()][119-end_position]
        # Castling check detection
        if abs(end_position-self.king_passant) < 2:
            score += pst['K'][119-end_position]

        piece = start_square.to_piece()
        # Castling
        if piece.is_king() and abs(initial_position-end_position) == 2:
            score += pst['R'][(initial_position+end_position)//2]
            score -= pst['R'][A1 if end_position < initial_position else H1]
        # Special pawn stuff
        if piece.is_pawn():
            if A8 <= end_position <= H8:
                score += pst['Q'][end_position] - pst['P'][end_position]
            if end_position == self.en_passant:
                score += pst['P'][119-(end_position+S)]
        return score


###############################################################################
# Search logic
###############################################################################

# lower <= s(pos) <= upper
Entry = namedtuple('Entry', 'lower upper')

# The normal OrderedDict doesn't update the position of a key in the list,
# when the value is changed.
class LRUCache:
    '''Store items in the order the keys were last added'''
    def __init__(self, size):
        self.od = OrderedDict()
        self.size = size

    def get(self, key, default=None):
        try: self.od.move_to_end(key)
        except KeyError: return default
        return self.od[key]

    def __setitem__(self, key, value):
        try: del self.od[key]
        except KeyError:
            if len(self.od) == self.size:
                self.od.popitem(last=False)
        self.od[key] = value

class Searcher:
    def __init__(self):
        # cache of (gamestate, plies to search, boolean if the game node is root) to (lower score, upper score)
        self.score_cache = LRUCache(TABLE_SIZE)
        # cache of gamestate to best move to make
        self.move_cache = LRUCache(TABLE_SIZE)
        self.nodes = 0

    def is_checkmated(self, gamestate):
        """
        Sunfish is a king-capture engine, so we should always check if we
        still have a king. Notice since this is the only termination check,
        the remaining code has to be comfortable with being mated, stalemated
        or able to capture the opponent king.
        """
        return gamestate.score <= -MATE_LOWER

    def get_cached_move(self, gamestate, boundary, depth, root):
        """
        Look in the table if we have already searched this position before.
        We also need to be sure, that the stored search was over the same
        nodes as the current search.
        """
        return self.score_cache.get((gamestate, depth, root), Entry(-MATE_UPPER, MATE_UPPER))

    def should_return_lower(self, entry, gamestate, boundary, depth, root):
        if entry.lower >= boundary:
            if (not root or self.move_cache.get(gamestate) is not None):
                return True

    def should_return_upper(self, entry, gamestate, boundary, depth, root):
        if entry.upper < boundary:
            return True

    def stalemate_handling(self, gamestate, target_score):
        """
        Stalemate checking is a bit tricky: Say we failed low, because
        we can't (legally) move and so the (real) score is -infty.
        At the next depth we are allowed to just return r, -infty <= r < boundary,
        which is normally fine.
        However, what if boundary = -10 and we don't have any legal moves?
        Then the score is actaully a draw and we should fail high!
        Thus, if target_score < boundary and target_score < 0 we need to double check what we are doing.
        This doesn't prevent sunfish from making a move that results in stalemate,
        but only if depth == 1, so that's probably fair enough.
        (Btw, at depth 1 we can also mate without realizing.)
        """
        is_dead = lambda gamestate: any(gamestate.value(m) >= MATE_LOWER for m in gamestate.gen_moves())
        if all(is_dead(gamestate.move(m)) for m in gamestate.gen_moves()):
            in_check = is_dead(gamestate.nullmove())
            target_score = -MATE_UPPER if in_check else 0
        return target_score

    def search(self, gamestate, secs):
        """
        Returns the best calulated move and its score.
        """
        start = time.time()
        for _ in self._search(gamestate):
            if time.time() - start > secs:
                break
        # If the game hasn't finished we can retrieve our move from the
        # transposition table.
        return self.move_cache.get(gamestate), self.score_cache.get((gamestate, self.depth, True)).lower

    def _search(self, gamestate):
        """
        Iterative deepening MTD-bi search

        References:
        * https://en.wikipedia.org/wiki/Minimax
        * https://en.wikipedia.org/wiki/MTD-f
        """
        self.nodes = 0

        # In finished games, we could potentially go far enough to cause a recursion
        # limit exception. Hence we bound the ply.
        for depth in range(1, 1000):
            self.depth = depth
            print("Now searching the next %s possible moves" % depth)
            # The inner loop is a binary search on the score of the game state.
            # Inv: lower <= score <= upper
            # 'while lower != upper' would work, but play tests show a margin of 20 plays better.
            lower, upper = -MATE_UPPER, MATE_UPPER
            while lower < upper - EVAL_ROUGHNESS:
                boundary = (lower+upper+1)//2
                score = self.bound(gamestate, boundary, depth)
                move = self.move_cache.get(gamestate)
                if move:
                    move = render(119-move[0]) + render(119-move[1])
                print("Now aiming for scores between %s and %s - I have found a possible score of %s. The current best move is " % (lower, upper, score) + move)
                if score >= boundary:
                    lower = score
                if score < boundary:
                    upper = score
            # We want to make sure the move to play hasn't been kicked out of the table,
            # So we make another call that must always fail high and thus produce a move.
            score = self.bound(gamestate, lower, depth)

            # Yield so the user may inspect the search
            yield

    def bound(self, gamestate, boundary, plies, root=True):
        """
        gamestate
        boundary: the threshold for success - if we can do better than this,
        plies: number of half-turns to search ahead
        root: is not a recursive call of this function

        returns r where
                gamestate.score <= r < boundary    if boundary > gamestate.score
                boundary <= r <= gamestate.score   if boundary <= gamestate.score
        """
        self.nodes += 1

        # Depth <= 0 is QSearch. Here any position is searched as deeply as is needed for calmness, and so there is no reason to keep different depths in the transposition table.
        plies = max(plies, 0)

        if self.is_checkmated(gamestate):
            return -MATE_UPPER

        entry = self.get_cached_move(gamestate, boundary, plies, root)
        if self.should_return_lower(entry, gamestate, boundary, plies, root):
            return entry.lower
        elif self.should_return_upper(entry, gamestate, boundary, plies, root):
            return entry.upper

        # Run through the moves, shortcutting when possible
        best = -MATE_UPPER
        for move, score in self.moves(gamestate, boundary, plies, root):
            best = max(best, score)
            if best >= boundary:
                # Save the move for pv construction and killer heuristic
                self.move_cache[gamestate] = move
                self.score_cache[(gamestate, plies, root)] = Entry(best, entry.upper)
                break

        if best < boundary and best < 0 and plies > 0:
            best = self.stalemate_handling(gamestate, best)

        if best < boundary:
            self.score_cache[(gamestate, plies, root)] = Entry(entry.lower, best)

        return best

    def moves(self, gamestate, boundary, plies, root):
        """
        Generator of moves to search in order.
        This allows us to define the moves, but only calculate them if needed.

        In base case with plies = 1, finds the best move possible in the gamestate and returns it + the score
        returns: best move, score that the move will yield
        """
        # First try not moving at all
        if plies > 0 and not root and any(c in gamestate.board.state for c in 'RBNQ'):
            yield None, -self.bound(gamestate.nullmove(), 1-boundary, plies-3, root=False)
        # For QSearch we have a different kind of null-move
        if plies == 0:
            yield None, gamestate.score
        # The best move found. Since this is just a cached move from the next for loop, it could be repeately yielded if does not satisfy boundary (not harmful). Note, we don't have to check for legality, since we've already done it before. Also note that in QS the killer must be a capture, otherwise we will be non deterministic.
        killer = self.move_cache.get(gamestate)
        if killer and (plies > 0 or gamestate.value(killer) >= QS_LIMIT):
            yield killer, -self.bound(gamestate.move(killer), 1-boundary, plies-1, root=False)
        # Then all the other moves
        for move in sorted(gamestate.gen_moves(), key=gamestate.value, reverse=True):
            if plies > 0 or gamestate.value(move) >= QS_LIMIT:
                yield move, -self.bound(gamestate.move(move), 1-boundary, plies-1, root=False)

###############################################################################
# User interface
###############################################################################

# Python 2 compatability
if sys.version_info[0] == 2:
    input = raw_input
    class NewOrderedDict(OrderedDict):
        def move_to_end(self, key):
            value = self.pop(key)
            self[key] = value
    OrderedDict = NewOrderedDict


def parse(c):
    fil, rank = ord(c[0]) - ord('a'), int(c[1]) - 1
    return A1 + fil - 10*rank


def render(i):
    rank, fil = divmod(i - A1, 10)
    return chr(fil + ord('a')) + str(-rank + 1)


def print_pos(gamestate):
    print()
    uni_pieces = {'R':'♜', 'N':'♞', 'B':'♝', 'Q':'♛', 'K':'♚', 'P':'♟',
                  'r':'♖', 'n':'♘', 'b':'♗', 'q':'♕', 'k':'♔', 'p':'♙', '.':'·'}
    for i, row in enumerate(gamestate.board.state.split()):
        print(' ', 8-i, ' '.join(uni_pieces.get(p, p) for p in row))
    print('    a b c d e f g h \n\n')

def test_moves(game_plan=False):
    return game_plan


game_plan=[]
def get_user_input(text):
    global game_plan
    if test_moves() and not game_plan:
        game_plan = test_moves()
    if game_plan:
        return game_plan.pop(0)
    return input(text)

def main():
    gamestate = GameState(board=Board(),
                    score=0,
                    castling_rights=(True,True),
                    opponent_castling_rights=(True,True),
                    en_passant=0,
                    king_passant=0
                    )
    searcher = Searcher()
    while True:
        print_pos(gamestate)

        if gamestate.score <= -MATE_LOWER:
            print("You lost")
            break

        # We query the user until she enters a (pseudo) legal move.
        move = None
        while move not in gamestate.gen_moves():
            match = re.match('([a-h][1-8])'*2, get_user_input('Your move: '))
            if match:
                move = parse(match.group(1)), parse(match.group(2))
            else:
                # Inform the user when invalid input (e.g. "help") is entered
                print("Please enter a move like g8f6")
        value = gamestate.value(move)
        gamestate = gamestate.move(move)
        print("Your Score: %s - that move's value was %s" % (0-gamestate.score, value))

        # After our move we rotate the board and print it again.
        # This allows us to see the effect of our move.
        print_pos(gamestate.rotate())

        if gamestate.score <= -MATE_LOWER:
            print("You won")
            break

        # Fire up the engine to look for a move.
        move, score = searcher.search(gamestate, secs=4)

        if score == MATE_UPPER:
            print("Checkmate!")

        # The black player moves from a rotated position, so we have to
        # 'back rotate' the move before printing it.
        print("My move:", render(119-move[0]) + render(119-move[1]))
        value = gamestate.value(move)
        gamestate = gamestate.move(move)
        print("My Score: %s - that move's value was %s" % (0-gamestate.score, value))


if __name__ == '__main__':
    main()
