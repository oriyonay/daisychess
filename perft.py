# daisychess: a tiny, perft-complete chess engine
# perft.py: contains only the chess logic and perft function for perft-testing.
# written by ori yonay
import copy

# ---------- some helper functions ---------- #
# get the rank number of a given square index
def rank_of(idx): return 8 - (idx // 8)

# ---------- end of  helper functions ---------- #
# a list to store all precalculated nonsliding piece destinations:
# (so NONSLIDING_DIRECTIONS['N'][sq] will contain all squares reachable by a knight on square sq)
NONSLIDING_DIRECTIONS = {'N' : [[] for _ in range(64)], 'K' : [[] for _ in range(64)]}
SLIDING_DIRECTIONS = {'R' : [[[],[],[],[]] for _ in range(64)], 'B' : [[[],[],[],[]] for _ in range(64)], 'Q' : [[] for _ in range(64)]}
CASTLE_SQUARES = {'w' : [(60, 62), (60, 58)], 'b' : [(59, 57), (59, 61)]}
CASTLE_EMPTY_SQUARES = {'w' : [(61, 62), (57, 58, 59)], 'b' : [(57, 58), (60, 61, 62)]}
CASTLE_SAFE_SQUARES = {'w' : [(61, 62), (58, 59)], 'b' : [(57, 58), (60, 61)]}
CASTLE_ROOK_SQUARES = {'w' : {'K' : (63, 61), 'Q' : (56, 59)}, 'b' : {'K' : (56, 58), 'Q' : (63, 60)}}

# if one of these rooks is moved or captured, which castle right is ruined?
# since we flip the board for each turn, this is also dependant on whose turn it is:
ROOK_SQUARE_CASTLE_RIGHT = {'w' : {0 : 'q', 7 : 'k', 56 : 'Q', 63 : 'K'},
                            'b' : {0 : 'k', 7 : 'q', 56 : 'K', 63 : 'Q'}
}

# function to precalculate tables, called on engine startup:
def init_all():
  # precalculate directions for nonsliding pieces
  for square in range(64):
    # initialize knight destination table:
    for offset in [-17, -15, -10, -6, 6, 10, 15, 17]:
      dest_square = square + offset
      # only add this destination square if it's valid:
      if dest_square in range(64) and abs((dest_square % 8) - (square % 8)) <= 2:
        NONSLIDING_DIRECTIONS['N'][square].append(dest_square)
    # initialize king destination table:
    for offset in [-9, -8, -7, -1, 1, 7, 8, 9]:
      dest_square = square + offset
      if dest_square in range(64) and abs((dest_square % 8) - (square % 8)) <= 1:
        NONSLIDING_DIRECTIONS['K'][square].append(dest_square)
    # initialize rook directions table:
    ranges = [range(square-8, -1, -8), range(square + 8, 64, 8), range(square + 1, 64), range(square - 1, -1, -1), range(square - 7, -1, -7), range(square - 9, -1, -9), range(square + 9, 64, 9), range(square + 7, 64, 7)]
    for i, r in enumerate(ranges):
      for dest_square in r:
        if i > 1 and dest_square % 8 == (0 if i%2 == 0 else 7): break
        SLIDING_DIRECTIONS['R' if i < 4 else 'B'][square][i%4].append(dest_square)
    # add directions to queen table:
    SLIDING_DIRECTIONS['Q'][square].extend(SLIDING_DIRECTIONS['R'][square])
    SLIDING_DIRECTIONS['Q'][square].extend(SLIDING_DIRECTIONS['B'][square])

class chess:
  # parse the FEN string for the position, the turn, and the castling rights:
  def __init__(self, FEN):
    FEN = FEN.split()
    self.board = FEN[0].replace('/', '')
    for i in range(1, 9):
      self.board = self.board.replace(str(i), '.' * i)
    self.board = list(self.board)
    self.turn, self.castle_rights = FEN[1], FEN[2] if FEN[1] == 'w' else FEN[2].swapcase()
    self.enpassant = -10 if FEN[3] == '-' else (ord(FEN[3][0]) - 97 if self.turn == 'w' else ord(FEN[3][0]) - 90)
    if self.turn == 'b': self.board = list((''.join(self.board[::-1]).swapcase()))

  # generate all pseudo-legal moves from this position as a pair of from_sq, to_sq index integers. yields 3 values: from_sq, to_sq, and move_type.
  # move_type can be None (normal move), 'C' for capture, 'P[PIECE TYPE]' (promotion), 'EP', 'PF' for pawn's first move, or 'K'/'Q' for castling
  def moves(self):
    global NONSLIDING_DIRECTIONS, SLIDING_DIRECTIONS
    self.king = self.board.index('K')
    for square, piece in enumerate(self.board):
      if piece.islower() or piece == '.': continue
      if piece == 'P':
        if self.board[square-8] == '.':
          if rank_of(square) == 7:
            for prom_piece in 'QNRB': yield square, square - 8, 'P%s' % prom_piece
          else: yield square, square - 8, None
        if rank_of(square) == 2 and self.board[square - 16] == '.' and self.board[square - 8] == '.': yield square, square - 16, 'PF'
        if self.board[square-7].islower() and square % 8 != 7:
          if rank_of(square) == 7:
            for prom_piece in 'QNRB': yield square, square - 7, 'P%s' % prom_piece
          else: yield square, square - 7, 'C'
        if self.board[square-9].islower() and square % 8 != 0:
          if rank_of(square) == 7:
            for prom_piece in 'QNRB': yield square, square - 9, 'P%s' % prom_piece
          else: yield square, square - 9, 'C'
        if abs((square % 8) - self.enpassant) == 1 and rank_of(square) == 5:
          yield square, 16 + self.enpassant, 'EP'
      elif piece in 'NK':
        for dest_square in NONSLIDING_DIRECTIONS[piece][square]:
          if self.board[dest_square].islower() or self.board[dest_square] == '.': yield square, dest_square, 'C' if self.board[dest_square].islower() else None
      else:
        for direction in SLIDING_DIRECTIONS[piece][square]:
          for dest_square in direction:
            if self.board[dest_square] == '.':
              yield square, dest_square, None
            elif self.board[dest_square].islower():
              yield square, dest_square, 'C'
              break
            else: break
    # add castle moves:
    if not self.attacked(self.king):
      for idx, side in enumerate('KQ'):
        if side in self.castle_rights and all([self.board[i] == '.' for i in CASTLE_EMPTY_SQUARES[self.turn][idx]]):
          if not any([self.attacked(sq) for sq in CASTLE_SAFE_SQUARES[self.turn][idx]]):
            yield *CASTLE_SQUARES[self.turn][idx], side

  # make the given move:
  def make_move(self, from_sq, to_sq, move_type):
    # do everything as if the move is normal:
    # captured = self.board[to_sq]
    self.board[from_sq], self.board[to_sq] = '.', self.board[from_sq]
    if self.board[to_sq] == 'K':
      self.king = to_sq
      self.castle_rights = ''.join(c for c in self.castle_rights if c.islower())
    if from_sq in [0, 7, 56, 63]: self.castle_rights = ''.join(c for c in self.castle_rights if c != ROOK_SQUARE_CASTLE_RIGHT[self.turn][from_sq])
    if to_sq in [0, 7, 56, 63]: self.castle_rights = ''.join(c for c in self.castle_rights if c != ROOK_SQUARE_CASTLE_RIGHT[self.turn][to_sq])

    self.enpassant = -10
    if move_type:
      if move_type == 'PF': self.enpassant = 7 - (to_sq % 8)
      elif move_type.startswith('P'): self.board[to_sq] = move_type[1]
      elif move_type == 'EP': self.board[to_sq+8] = '.'
      elif move_type == 'C': pass
      else:
        rook_start, rook_end = CASTLE_ROOK_SQUARES[self.turn][move_type]
        self.board[rook_start], self.board[rook_end] = self.board[rook_end], self.board[rook_start]
        self.castle_rights = ''.join(c for c in self.castle_rights if c.islower())

    # this move is only legal if the king is not in check:
    is_check = self.attacked(self.king)

    # flip the turn and the board:
    self.turn = 'w' if self.turn == 'b' else 'b'
    self.board = list((''.join(self.board[::-1]).swapcase()))
    self.castle_rights = self.castle_rights.swapcase()

    # this is legal if and only if the king is not in check:
    return not is_check


  # is the current square attacked?
  def attacked(self, square):
    if self.board[square-7] == 'p' and square % 8 != 7: return True
    if self.board[square-9] == 'p' and square % 8 != 0: return True
    for nonsliding_piece in 'NK':
      for dest_square in NONSLIDING_DIRECTIONS[nonsliding_piece][square]:
        if self.board[dest_square] == nonsliding_piece.lower(): return True
    for sliding_piece in 'RBQ':
      for direction in SLIDING_DIRECTIONS[sliding_piece][square]:
        for dest_square in direction:
          if self.board[dest_square] in [sliding_piece.lower(), 'q']: return True
          if self.board[dest_square] != '.': break
    return False

  # to print the board:
  def show(self):
    for i in range(0, 64, 8): print(' '.join(self.board[i:i+8]))
    print('\nturn: %s' % self.turn)
    print('castle rights: %s\n' % self.castle_rights)

def perft(board, depth):
  if depth == 0: return 1
  count = 0
  for from_sq, to_sq, move_type in board.moves():
    board_copy = copy.deepcopy(board)
    legal = board_copy.make_move(from_sq, to_sq, move_type)
    if legal:
      count += perft(board_copy, depth - 1)
  return count

if __name__ == '__main__':
  init_all()
  board = chess('rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1 ')
  print(perft(board, 3))
