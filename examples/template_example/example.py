def print_board(board):
    """
    Display the current state of the tic-tac-toe board.
    
    Args:
        board (list): A list of 9 elements representing the board state.
                     Each element is either 'X', 'O', or ' ' (empty).
    """
    print("\nCurrent board:")
    for i in range(0, 9, 3):
        print(" | ".join(board[i:i+3]))
    print()
def check_winner(board, player):
    """
    Check if the specified player has won the game.
    
    Args:
        board (list): A list of 9 elements representing the board state.
        player (str): The player to check for ('X' or 'O').
    
    Returns:
        bool: True if the player has won, False otherwise.
    """
    # Define all possible winning combinations
    win_conditions = [
        (0, 1, 2), (3, 4, 5), (6, 7, 8),  # Rows
        (0, 3, 6), (1, 4, 7), (2, 5, 8),  # Columns
        (0, 4, 8), (2, 4, 6)              # Diagonals
    ]
    return any(all(board[pos] == player for pos in condition) for condition in win_conditions)
def computer_move(board):
    """
    Execute the computer's move with basic AI strategy.
    
    Strategy:
        1. Try to win: If there's a winning move, take it.
        2. Block opponent: If the opponent can win next turn, block them.
        3. Take any available space: Otherwise, take the first available space.
    
    Args:
        board (list): A list of 9 elements representing the board state.
                     The board is modified in place.
    """
    # Strategy 1: Try to win
    for i in range(9):
        if board[i] == " ":
            board[i] = "O"
            if check_winner(board, "O"):
                return
            board[i] = " "
    
    # Strategy 2: Block the opponent from winning
    for i in range(9):
        if board[i] == " ":
            board[i] = "X"
            if check_winner(board, "X"):
                board[i] = "O"
                return
            board[i] = " "
    
    # Strategy 3: Take the first available space
    for i in range(9):
        if board[i] == " ":
            board[i] = "O"
            return
def main():
    """
    Main game loop for Tic-Tac-Toe.
    
    Handles the game flow including:
        - Player input and validation
        - Turn alternation between player and computer
        - Win/tie condition checking
        - Game state display
    """
    # Initialize an empty 3x3 board
    board = [" "] * 9
    
    # Display game instructions
    print("Tic Tac Toe: You are X, Computer is O.")
    print("Enter a move (0-8) corresponding to the board positions:")
    print("0 | 1 | 2")
    print("3 | 4 | 5")
    print("6 | 7 | 8")
    
    # Main game loop
    while True:
        # Display current board state
        print_board(board)
        
        # Get and validate user input
        user_move = input("Your move (0-8): ")
        if not user_move.isdigit() or int(user_move) not in range(9):
            print("Invalid input. Please enter a digit from 0 to 8.")
            continue
        
        user_move = int(user_move)
        
        # Check if the chosen space is available
        if board[user_move] != " ":
            print("That space is already taken. Try again.")
            continue
        
        # Execute player's move
        board[user_move] = "X"
        
        # Check if player won
        if check_winner(board, "X"):
            print_board(board)
            print("You win! 🎉")
            break
        
        # Check for tie after player's move
        if all(cell != " " for cell in board):
            print_board(board)
            print("It's a tie!")
            break
        
        # Execute computer's move
        computer_move(board)
        
        # Check if computer won
        if check_winner(board, "O"):
            print_board(board)
            print("Computer wins! 🤖")
            break
        
        # Check for tie after computer's move
        if all(cell != " " for cell in board):
            print_board(board)
            print("It's a tie!")
            break
if __name__ == "__main__":
    # Entry point: Run the game when script is executed directly
    main()