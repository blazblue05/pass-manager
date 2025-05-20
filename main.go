package main

import (
	"bytes" // For PKCS#7 padding
	"crypto/aes"
	"crypto/cipher"
	"crypto/hmac" // Added from snippet
	"crypto/rand"
	"crypto/sha256" // Added from snippet
	"encoding/hex"  // Added for hex encoding/decoding
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"time"

	"fyne.io/fyne/v2"
	"fyne.io/fyne/v2/app"
	"fyne.io/fyne/v2/container"
	"fyne.io/fyne/v2/dialog"
	"fyne.io/fyne/v2/layout"
	"fyne.io/fyne/v2/widget"
	"golang.org/x/crypto/argon2"
	"golang.org/x/crypto/bcrypt"
)

// User represents a user of the password manager
type User struct {
	Username string
}

// StoredUser represents a user as stored in the database
type StoredUser struct {
	Username       string
	PasswordHash   string
	Salt           []byte
	FailedAttempts int
	LockoutExpiry  time.Time
}

// PasswordEntry represents a stored password
type PasswordEntry struct {
	Title    string
	Username string
	Password string // Stores hex encoded (IV + AES-CBC-EncryptedPaddedData + HMAC-Tag)
	URL      string
	Notes    string
}

// PasswordManager handles the storage and retrieval of passwords
type PasswordManager struct {
	CurrentUser *User
	Entries     []PasswordEntry
	MasterKey   []byte // Will be 64 bytes: 32 for AES, 32 for HMAC
	LoggedIn    bool
	Users       map[string]StoredUser
	DataDir     string
}

// NewPasswordManager creates a new password manager
func NewPasswordManager() *PasswordManager {
	homeDir, err := os.UserHomeDir()
	if err != nil {
		fmt.Printf("Warning: Could not get home directory: %v. Using current directory.\n", err)
		homeDir = "."
	}
	dataDir := filepath.Join(homeDir, ".pass-manager-data")
	if err := os.MkdirAll(dataDir, 0700); err != nil {
		fmt.Printf("Fatal: Could not create data directory '%s': %v\n", dataDir, err)
		os.Exit(1)
	}
	fmt.Printf("DEBUG: Data directory: %s\n", dataDir)
	pm := &PasswordManager{
		Entries: make([]PasswordEntry, 0),
		Users:   make(map[string]StoredUser),
		DataDir: dataDir,
	}
	fmt.Println("DEBUG: Attempting to load users...")
	if err := pm.loadUsers(); err != nil {
		if !os.IsNotExist(err) {
			fmt.Printf("Warning: Could not load users: %v\n", err)
		} else {
			fmt.Println("DEBUG: users.json does not exist yet.")
		}
	} else {
		fmt.Printf("DEBUG: Loaded %d users.\n", len(pm.Users))
	}
	return pm
}

func (pm *PasswordManager) loadUsers() error {
	usersFile := filepath.Join(pm.DataDir, "users.json")
	data, err := os.ReadFile(usersFile)
	if err != nil {
		return err
	}
	if len(data) == 0 {
		pm.Users = make(map[string]StoredUser)
		return nil
	}
	return json.Unmarshal(data, &pm.Users)
}

func (pm *PasswordManager) saveUsers() error {
	usersFile := filepath.Join(pm.DataDir, "users.json")
	if pm.Users == nil {
		pm.Users = make(map[string]StoredUser)
	}
	data, err := json.MarshalIndent(pm.Users, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal users: %w", err)
	}
	return os.WriteFile(usersFile, data, 0600)
}

// sanitizeFilename removes or replaces characters that could be used for path traversal
// or are otherwise unsafe in filenames
func sanitizeFilename(filename string) string {
	// Replace any character that isn't alphanumeric, underscore, or hyphen with an underscore
	// This prevents path traversal attacks (../../etc) and other unsafe filename characters
	safeFilename := ""
	for _, r := range filename {
		if (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9') || r == '_' || r == '-' {
			safeFilename += string(r)
		} else {
			safeFilename += "_"
		}
	}

	// Ensure the filename isn't empty after sanitization
	if safeFilename == "" {
		safeFilename = "user"
	}

	return safeFilename
}

func (pm *PasswordManager) loadEntries() error {
	if pm.CurrentUser == nil || pm.CurrentUser.Username == "" {
		return fmt.Errorf("no user logged in")
	}
	// Sanitize username before using it in a filename
	safeUsername := sanitizeFilename(pm.CurrentUser.Username)
	entriesFile := filepath.Join(pm.DataDir, fmt.Sprintf("%s_entries.json", safeUsername))
	data, err := os.ReadFile(entriesFile)
	if err != nil {
		if os.IsNotExist(err) {
			pm.Entries = make([]PasswordEntry, 0)
			return nil
		}
		return fmt.Errorf("failed to read entries file: %w", err)
	}
	if len(data) == 0 {
		pm.Entries = make([]PasswordEntry, 0)
		return nil
	}
	pm.Entries = make([]PasswordEntry, 0)
	err = json.Unmarshal(data, &pm.Entries)
	if err != nil {
		return fmt.Errorf("failed to unmarshal entries: %w", err)
	}
	return nil
}

func (pm *PasswordManager) saveEntries() error {
	if pm.CurrentUser == nil || pm.CurrentUser.Username == "" {
		return fmt.Errorf("no user logged in to save entries for")
	}
	// Sanitize username before using it in a filename
	safeUsername := sanitizeFilename(pm.CurrentUser.Username)
	entriesFile := filepath.Join(pm.DataDir, fmt.Sprintf("%s_entries.json", safeUsername))
	if pm.Entries == nil {
		pm.Entries = make([]PasswordEntry, 0)
	}
	data, err := json.MarshalIndent(pm.Entries, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal entries: %w", err)
	}
	return os.WriteFile(entriesFile, data, 0600)
}

func generateSalt() ([]byte, error) {
	salt := make([]byte, 16)
	if _, err := io.ReadFull(rand.Reader, salt); err != nil {
		return nil, fmt.Errorf("failed to generate salt: %w", err)
	}
	return salt, nil
}

// Modified deriveMasterKey to produce longer key (now 64 bytes) as per snippet's implication
func deriveMasterKey(password string, salt []byte) []byte {
	fmt.Println("DEBUG: Deriving 64-byte master key using Argon2id...")
	timeCost := uint32(3)    // Iterations - consider increasing
	memoryCost := uint32(64) // Memory cost in KiB (64 MiB) - consider increasing
	parallelism := uint8(4)  // Number of threads
	keyLen := uint32(64)     // NEW: 64 bytes for combined encryption and HMAC keys

	key := argon2.IDKey(
		[]byte(password),
		salt,
		timeCost,
		memoryCost*1024, // Argon2 expects memory in KiB. Snippet had `memoryCost*1204`, corrected to 1024.
		parallelism,
		keyLen,
	)

	clearString(&password) // Assuming this is a placeholder for secure password handling
	fmt.Println("DEBUG: 64-byte Master key derived.")
	return key
}

func (pm *PasswordManager) Register(username, password string) error {
	// Validate username before registration
	if username == "" || password == "" {
		return fmt.Errorf("username and password cannot be empty")
	}

	// Check if username contains only safe characters
	safeUsername := sanitizeFilename(username)
	if safeUsername != username {
		return fmt.Errorf("username contains invalid characters; only alphanumeric, underscore, and hyphen are allowed")
	}

	if _, exists := pm.Users[username]; exists {
		return fmt.Errorf("username '%s' already exists", username)
	}

	salt, err := generateSalt()
	if err != nil {
		return fmt.Errorf("failed to generate salt: %w", err)
	}
	hashedPassword, err := bcrypt.GenerateFromPassword([]byte(password), bcrypt.DefaultCost)
	if err != nil {
		clearString(&password)
		return fmt.Errorf("failed to hash password: %w", err)
	}
	pm.Users[username] = StoredUser{
		Username:       username,
		PasswordHash:   string(hashedPassword),
		Salt:           salt,
		FailedAttempts: 0,
		LockoutExpiry:  time.Time{},
	}
	if err := pm.saveUsers(); err != nil {
		clearString(&password)
		return fmt.Errorf("failed to save user data: %w", err)
	}
	pm.CurrentUser = &User{Username: username}
	pm.MasterKey = deriveMasterKey(password, salt) // This will now be 64 bytes
	pm.LoggedIn = true
	pm.Entries = make([]PasswordEntry, 0)
	if err := pm.saveEntries(); err != nil {
		fmt.Printf("Warning: Could not create initial empty entries file for %s: %v\n", username, err)
	}
	return nil
}

func (pm *PasswordManager) Login(username, password string) error {
	u, exists := pm.Users[username]
	if !exists {
		clearString(&password)
		return fmt.Errorf("user not found")
	}
	now := time.Now()
	if u.LockoutExpiry.After(now) {
		clearString(&password)
		return fmt.Errorf("Account locked until %v", u.LockoutExpiry.Format(time.RFC822))
	}
	err := bcrypt.CompareHashAndPassword([]byte(u.PasswordHash), []byte(password))
	if err != nil {
		u.FailedAttempts++
		const maxAttempts = 5
		if u.FailedAttempts >= maxAttempts {
			lockDuration := time.Minute * 10
			u.LockoutExpiry = now.Add(lockDuration)
		}
		pm.Users[username] = u
		_ = pm.saveUsers()
		clearString(&password)
		if errors.Is(err, bcrypt.ErrMismatchedHashAndPassword) {
			return errors.New("Incorrect password")
		}
		return fmt.Errorf("password verification failed: %w", err)
	} else {
		u.FailedAttempts = 0
		u.LockoutExpiry = time.Time{}
		pm.Users[username] = u
		_ = pm.saveUsers()
		pm.CurrentUser = &User{Username: username}
		pm.LoggedIn = true
		pm.MasterKey = deriveMasterKey(password, u.Salt) // This will now be 64 bytes
		if errLoad := pm.loadEntries(); errLoad != nil {
			fmt.Printf("Warning: Could not load entries for user %s after login: %v\n", username, errLoad)
			pm.Entries = make([]PasswordEntry, 0)
		}
		return nil
	}
}

// --- PKCS#7 Padding Helpers ---
func pkcs7Pad(data []byte, blockSize int) ([]byte, error) {
	if blockSize <= 0 {
		return nil, errors.New("invalid block size")
	}
	padding := blockSize - (len(data) % blockSize)
	padText := bytes.Repeat([]byte{byte(padding)}, padding)
	return append(data, padText...), nil
}

func pkcs7Unpad(data []byte, blockSize int) ([]byte, error) {
	if blockSize <= 0 {
		return nil, errors.New("invalid block size")
	}
	if len(data) == 0 {
		return nil, errors.New("data is empty")
	}
	if len(data)%blockSize != 0 {
		// This can happen if the ciphertext was corrupted or not padded correctly.
		return nil, errors.New("data is not block-aligned, cannot unpad")
	}
	padding := int(data[len(data)-1])
	if padding > blockSize || padding == 0 {
		return nil, errors.New("invalid padding value")
	}
	// Check all padding bytes
	for i := len(data) - padding; i < len(data); i++ {
		if int(data[i]) != padding {
			return nil, errors.New("invalid padding bytes")
		}
	}
	return data[:len(data)-padding], nil
}

// EncryptPassword with IV and HMAC verification, returns hex string
// This replaces the old Encrypt function and the previous EncryptPassword
func (pm *PasswordManager) EncryptPassword(plaintextString string) (string, error) {
	fmt.Println("DEBUG: EncryptPassword (AES-CBC-HMAC) called.")
	if pm.MasterKey == nil || len(pm.MasterKey) != 64 {
		return "", errors.New("master key not initialized correctly for encryption (expected 64 bytes)")
	}
	plaintext := []byte(plaintextString)
	encryptionKey := pm.MasterKey[:32] // First 32 bytes for AES-256
	hmacKey := pm.MasterKey[32:]       // Next 32 bytes for HMAC-SHA256

	// Pad plaintext
	paddedPlaintext, err := pkcs7Pad(plaintext, aes.BlockSize)
	if err != nil {
		return "", fmt.Errorf("failed to pad plaintext: %w", err)
	}

	// Generate IV
	iv := make([]byte, aes.BlockSize) // AES block size is 16 bytes
	if _, err := io.ReadFull(rand.Reader, iv); err != nil {
		return "", fmt.Errorf("failed to generate IV: %w", err)
	}

	// Encrypt using AES-256-CBC
	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return "", fmt.Errorf("failed to create AES cipher: %w", err)
	}
	ciphertext := make([]byte, len(paddedPlaintext))
	cbcEnc := cipher.NewCBCEncrypter(block, iv)
	cbcEnc.CryptBlocks(ciphertext, paddedPlaintext)

	// Compute HMAC over IV and ciphertext
	h := hmac.New(sha256.New, hmacKey)
	_, _ = h.Write(iv) // Include IV in HMAC
	_, _ = h.Write(ciphertext)
	tag := h.Sum(nil)

	// Prepend IV and append tag: IV (16 bytes) + Ciphertext + Tag (32 bytes)
	encryptedData := append(iv, ciphertext...)
	encryptedData = append(encryptedData, tag...)

	return hex.EncodeToString(encryptedData), nil
}

// DecryptPassword with HMAC verification first, expects hex string
// This replaces the old Decrypt function and the previous DecryptPassword
func (pm *PasswordManager) DecryptPassword(hexEncodedEncryptedData string) (string, error) {
	fmt.Println("DEBUG: DecryptPassword (AES-CBC-HMAC) called.")
	if pm.MasterKey == nil || len(pm.MasterKey) != 64 {
		return "", errors.New("master key not initialized correctly for decryption (expected 64 bytes)")
	}

	encryptedData, err := hex.DecodeString(hexEncodedEncryptedData)
	if err != nil {
		return "", fmt.Errorf("failed to decode hex data: %w", err)
	}

	ivSize := aes.BlockSize // 16 bytes
	tagSize := sha256.Size  // 32 bytes

	if len(encryptedData) < ivSize+tagSize {
		return "", errors.New("invalid encrypted data format: too short")
	}

	iv := encryptedData[:ivSize]
	ciphertext := encryptedData[ivSize : len(encryptedData)-tagSize]
	receivedTag := encryptedData[len(encryptedData)-tagSize:]

	// Verify HMAC first
	encryptionKey := pm.MasterKey[:32] // For AES cipher
	hmacKey := pm.MasterKey[32:]       // For HMAC verification

	h := hmac.New(sha256.New, hmacKey)
	_, _ = h.Write(iv) // Include IV in HMAC verification
	_, _ = h.Write(ciphertext)
	expectedTag := h.Sum(nil)

	if !hmac.Equal(expectedTag, receivedTag) {
		return "", errors.New("HMAC verification failed: data integrity compromised")
	}

	// Proceed to decrypt only after successful verification
	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return "", fmt.Errorf("failed to create AES cipher for decryption: %w", err)
	}
	if len(ciphertext)%aes.BlockSize != 0 {
		// This check is important before CBC decryption
		return "", errors.New("ciphertext is not a multiple of the block size")
	}
	cbcDec := cipher.NewCBCDecrypter(block, iv)
	paddedPlaintext := make([]byte, len(ciphertext))
	cbcDec.CryptBlocks(paddedPlaintext, ciphertext)

	// Unpad plaintext
	plaintext, err := pkcs7Unpad(paddedPlaintext, aes.BlockSize)
	if err != nil {
		return "", fmt.Errorf("failed to unpad plaintext: %w", err)
	}

	return string(plaintext), nil
}

func (pm *PasswordManager) AddEntry(title, username, password, url, notes string) error {
	if !pm.LoggedIn {
		return fmt.Errorf("must be logged in to add entries")
	}
	if title == "" {
		return fmt.Errorf("entry title cannot be empty")
	}

	// Use new EncryptPassword which returns hex string
	encryptedPasswordHex, err := pm.EncryptPassword(password)
	if err != nil {
		clearString(&password)
		return fmt.Errorf("failed to encrypt password for entry '%s': %w", title, err)
	}
	clearString(&password)

	entry := PasswordEntry{
		Title:    title,
		Username: username,
		Password: encryptedPasswordHex, // Store hex encoded string
		URL:      url,
		Notes:    notes,
	}
	pm.Entries = append(pm.Entries, entry)
	return pm.saveEntries()
}

func (pm *PasswordManager) GetEntries() []PasswordEntry {
	if pm.Entries == nil {
		return make([]PasswordEntry, 0)
	}
	return pm.Entries
}

func (pm *PasswordManager) GetDecryptedPassword(index int) (string, error) {
	if !pm.LoggedIn {
		return "", fmt.Errorf("not logged in")
	}
	if index < 0 || index >= len(pm.Entries) {
		return "", fmt.Errorf("invalid entry index: %d", index)
	}
	encryptedPasswordHex := pm.Entries[index].Password
	if encryptedPasswordHex == "" {
		return "", nil
	}
	// Use new DecryptPassword which expects hex string
	return pm.DecryptPassword(encryptedPasswordHex)
}

func (pm *PasswordManager) DeleteEntry(index int) error {
	if !pm.LoggedIn {
		return fmt.Errorf("must be logged in to delete entries")
	}
	if index < 0 || index >= len(pm.Entries) {
		return fmt.Errorf("invalid entry index: %d", index)
	}
	pm.Entries = append(pm.Entries[:index], pm.Entries[index+1:]...)
	return pm.saveEntries()
}

func (pm *PasswordManager) UpdateEntry(index int, title, username, password, url, notes string) error {
	if !pm.LoggedIn {
		return fmt.Errorf("must be logged in to update entries")
	}
	if index < 0 || index >= len(pm.Entries) {
		return fmt.Errorf("invalid entry index: %d", index)
	}
	if title == "" {
		return fmt.Errorf("entry title cannot be empty")
	}

	// Use new EncryptPassword which returns hex string
	encryptedPasswordHex, err := pm.EncryptPassword(password)
	if err != nil {
		clearString(&password)
		return fmt.Errorf("failed to encrypt password for update on '%s': %w", title, err)
	}
	clearString(&password)

	pm.Entries[index] = PasswordEntry{
		Title:    title,
		Username: username,
		Password: encryptedPasswordHex, // Store hex encoded string
		URL:      url,
		Notes:    notes,
	}
	return pm.saveEntries()
}

// Logout securely logs out the current user, clearing sensitive data from memory
func (pm *PasswordManager) Logout() {
	fmt.Println("DEBUG: Logging out...")
	if pm.MasterKey != nil {
		fmt.Println("DEBUG: Clearing master key...")
		clearBytes(pm.MasterKey)
		pm.MasterKey = nil
	}
	pm.CurrentUser = nil
	pm.LoggedIn = false
	if pm.Entries != nil {
		fmt.Println("DEBUG: Clearing entries from memory...")
		pm.Entries = make([]PasswordEntry, 0)
	}
	fmt.Println("DEBUG: Logout complete.")
}

func clearString(s *string) {
	if s == nil {
		return
	}
	*s = ""
}

func clearBytes(b []byte) {
	for i := range b {
		b[i] = 0
	}
}

func GeneratePassword(length int, useUppercase, useLowercase, useNumbers, useSpecial bool) (string, error) {
	if length < 12 {
		return "", fmt.Errorf("password length must be at least 12 characters")
	}
	const lowercaseChars = "abcdefghijklmnopqrstuvwxyz"
	const uppercaseChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
	const numberChars = "0123456789"
	const specialChars = "!@#$%^&*()_+-=[]{}|;:,.<>?"
	var requiredChars []byte
	var allChars string
	if useLowercase {
		allChars += lowercaseChars
		randIndex, _ := rand.Int(rand.Reader, big.NewInt(int64(len(lowercaseChars))))
		requiredChars = append(requiredChars, lowercaseChars[randIndex.Int64()])
	}
	if useUppercase {
		allChars += uppercaseChars
		randIndex, _ := rand.Int(rand.Reader, big.NewInt(int64(len(uppercaseChars))))
		requiredChars = append(requiredChars, uppercaseChars[randIndex.Int64()])
	}
	if useNumbers {
		allChars += numberChars
		randIndex, _ := rand.Int(rand.Reader, big.NewInt(int64(len(numberChars))))
		requiredChars = append(requiredChars, numberChars[randIndex.Int64()])
	}
	if useSpecial {
		allChars += specialChars
		randIndex, _ := rand.Int(rand.Reader, big.NewInt(int64(len(specialChars))))
		requiredChars = append(requiredChars, specialChars[randIndex.Int64()])
	}
	if allChars == "" {
		return "", fmt.Errorf("at least one character set must be selected")
	}
	if length < len(requiredChars) {
		return "", fmt.Errorf("password length is too short to include all required character types")
	}
	remainingLength := length - len(requiredChars)
	randomChars := make([]byte, remainingLength)
	for i := 0; i < remainingLength; i++ {
		randNum, err := rand.Int(rand.Reader, big.NewInt(int64(len(allChars))))
		if err != nil {
			return "", fmt.Errorf("failed to generate random character index: %w", err)
		}
		randomChars[i] = allChars[randNum.Int64()]
	}
	passwordBytes := append(requiredChars, randomChars...)
	for i := len(passwordBytes) - 1; i > 0; i-- {
		jBig, err := rand.Int(rand.Reader, big.NewInt(int64(i+1)))
		if err != nil {
			return "", fmt.Errorf("failed to generate shuffle index: %w", err)
		}
		j := jBig.Int64()
		passwordBytes[i], passwordBytes[j] = passwordBytes[j], passwordBytes[i]
	}
	password := string(passwordBytes)
	clearBytes(passwordBytes)
	clearBytes(requiredChars)
	clearBytes(randomChars)
	return password, nil
}

// --- Main GUI Application ---
func main() {
	pm := NewPasswordManager()
	a := app.New()
	w := a.NewWindow("Password Manager")
	w.Resize(fyne.NewSize(800, 600))

	usernameLoginEntry := widget.NewEntry()
	usernameLoginEntry.SetPlaceHolder("Username")
	passwordLoginEntry := widget.NewPasswordEntry()
	passwordLoginEntry.SetPlaceHolder("Password")
	loginStatusLabel := widget.NewLabel("")

	titleEntry := widget.NewEntry()
	titleEntry.SetPlaceHolder("Title")
	usernameEntryMain := widget.NewEntry()
	usernameEntryMain.SetPlaceHolder("Entry Username")
	passwordEntryMain := widget.NewPasswordEntry()
	passwordEntryMain.SetPlaceHolder("*** ENCRYPTED ***")
	passwordEntryMain.Disable()
	urlEntry := widget.NewEntry()
	urlEntry.SetPlaceHolder("URL")
	notesEntry := widget.NewMultiLineEntry()
	notesEntry.SetPlaceHolder("Notes")
	notesEntry.Wrapping = fyne.TextWrapWord

	loginBtn := widget.NewButton("Login", func() {})
	registerBtn := widget.NewButton("Register", func() {})
	addBtn := widget.NewButton("Add New Entry", func() {})
	saveBtn := widget.NewButton("Save Changes", func() {})
	saveBtn.Disable()
	deleteBtn := widget.NewButton("Delete Entry", func() {})
	deleteBtn.Disable()
	viewPasswordBtn := widget.NewButton("View/Copy Password", func() {})
	viewPasswordBtn.Disable()
	generatePasswordBtn := widget.NewButton("Generate", func() {})
	logoutBtn := widget.NewButton("Logout", func() {})
	clearFormBtn := widget.NewButton("Clear Form / New", func() {})

	lengthEntry := widget.NewEntry()
	lengthEntry.SetText("16")
	useUppercaseCheck := widget.NewCheck("Uppercase", nil)
	useUppercaseCheck.SetChecked(true)
	useLowercaseCheck := widget.NewCheck("Lowercase", nil)
	useLowercaseCheck.SetChecked(true)
	useNumbersCheck := widget.NewCheck("Numbers", nil)
	useNumbersCheck.SetChecked(true)
	useSpecialCheck := widget.NewCheck("Special", nil)
	useSpecialCheck.SetChecked(true)
	generatedPasswordEntry := widget.NewEntry()
	generatedPasswordEntry.SetPlaceHolder("Generated password appears here")
	generatedPasswordEntry.Disable()

	var copyGeneratedBtn *widget.Button
	copyGeneratedBtn = widget.NewButton("Copy to Entry Field", func() {
		if generatedPasswordEntry.Text != "" {
			passwordEntryMain.SetText(generatedPasswordEntry.Text)
			passwordEntryMain.Enable()
			generatedPasswordEntry.SetText("")
			copyGeneratedBtn.Disable()
		}
	})
	copyGeneratedBtn.Disable()

	var selectedIndex int = -1
	entriesList := widget.NewList(
		func() int { return len(pm.GetEntries()) },
		func() fyne.CanvasObject {
			return container.NewHBox(widget.NewLabel("Template Title"), layout.NewSpacer(), widget.NewLabel("Template URL"))
		},
		func(id widget.ListItemID, obj fyne.CanvasObject) {
			entries := pm.GetEntries()
			if id >= 0 && id < len(entries) {
				hbox := obj.(*fyne.Container)
				titleLabel := hbox.Objects[0].(*widget.Label)
				urlLabel := hbox.Objects[2].(*widget.Label)
				titleLabel.SetText(entries[id].Title)
				urlLabel.SetText(entries[id].URL)
			} else {
				hbox := obj.(*fyne.Container)
				titleLabel := hbox.Objects[0].(*widget.Label)
				urlLabel := hbox.Objects[2].(*widget.Label)
				titleLabel.SetText("---")
				urlLabel.SetText("---")
			}
		},
	)

	clearFieldsAndSelection := func() {
		titleEntry.SetText("")
		usernameEntryMain.SetText("")
		passwordEntryMain.SetText("")
		passwordEntryMain.SetPlaceHolder("*** ENCRYPTED ***")
		passwordEntryMain.Disable()
		urlEntry.SetText("")
		notesEntry.SetText("")
		selectedIndex = -1
		entriesList.UnselectAll()
		saveBtn.Disable()
		deleteBtn.Disable()
		viewPasswordBtn.Disable()
		addBtn.Enable()
		generatedPasswordEntry.SetText("")
		copyGeneratedBtn.Disable()
	}

	refreshListAndClear := func() {
		entriesList.Refresh()
		clearFieldsAndSelection()
	}

	loginFields := container.NewVBox(
		widget.NewLabel("Username"), usernameLoginEntry,
		widget.NewLabel("Password"), passwordLoginEntry,
	)
	loginForm := container.NewVBox(
		widget.NewLabel("Login or Register"),
		loginFields,
		loginStatusLabel,
		container.NewGridWithColumns(2, loginBtn, registerBtn),
	)
	loginContainer := container.NewVBox(
		layout.NewSpacer(),
		container.NewHBox(layout.NewSpacer(), loginForm, layout.NewSpacer()),
		layout.NewSpacer(),
	)

	generatorFormWidgets := widget.NewForm(
		widget.NewFormItem("Length", lengthEntry),
		widget.NewFormItem("Options", container.NewVBox(
			useUppercaseCheck, useLowercaseCheck, useNumbersCheck, useSpecialCheck,
		)),
	)
	generatorContainer := container.NewVBox(
		widget.NewLabel("Password Generator"),
		generatorFormWidgets,
		generatePasswordBtn,
		generatedPasswordEntry,
		copyGeneratedBtn,
	)

	detailsForm := container.NewVBox(
		widget.NewLabel("Entry Details"),
		widget.NewForm(
			widget.NewFormItem("Title", titleEntry),
			widget.NewFormItem("Username", usernameEntryMain),
			widget.NewFormItem("Password", container.NewBorder(nil, nil, nil, viewPasswordBtn, passwordEntryMain)),
			widget.NewFormItem("URL", urlEntry),
			widget.NewFormItem("Notes", notesEntry),
		),
		container.NewGridWithColumns(3, addBtn, saveBtn, deleteBtn),
		clearFormBtn,
		widget.NewSeparator(),
		generatorContainer,
	)

	loggedInUsernameLabel := widget.NewLabel("Logged in as: ?")
	topBar := container.NewBorder(nil, nil, loggedInUsernameLabel, logoutBtn, widget.NewLabel("Password Manager"))
	mainContentSplit := container.NewHSplit(
		container.NewBorder(nil, nil, nil, nil, entriesList),
		container.NewPadded(detailsForm),
	)
	mainContentSplit.SetOffset(0.35)
	mainContainer := container.NewBorder(topBar, nil, nil, nil, mainContentSplit)

	loginBtn.OnTapped = func() {
		loginStatusLabel.SetText("Logging in...")
		username := usernameLoginEntry.Text
		password := passwordLoginEntry.Text
		errLogin := pm.Login(username, password)
		if errLogin == nil {
			loggedInUsernameLabel.SetText("Logged in as: " + pm.CurrentUser.Username)
			passwordLoginEntry.SetText("")
			loginStatusLabel.SetText("")
			refreshListAndClear()
			w.SetContent(mainContainer)
		} else {
			passwordLoginEntry.SetText("")
			loginStatusLabel.SetText(errLogin.Error())
			dialog.ShowError(errLogin, w)
		}
		clearString(&password)
	}

	registerBtn.OnTapped = func() {
		username := usernameLoginEntry.Text
		password := passwordLoginEntry.Text
		if username == "" || password == "" {
			dialog.ShowError(fmt.Errorf("username and password cannot be empty"), w)
			return
		}
		loginStatusLabel.SetText("Registering...")
		err := pm.Register(username, password)
		if err != nil {
			dialog.ShowError(fmt.Errorf("registration failed: %w", err), w)
			loginStatusLabel.SetText("Registration failed.")
		} else {
			loggedInUsernameLabel.SetText("Logged in as: " + pm.CurrentUser.Username)
			passwordLoginEntry.SetText("")
			loginStatusLabel.SetText("")
			refreshListAndClear()
			w.SetContent(mainContainer)
			dialog.ShowInformation("Success", "Registration successful! You are now logged in.", w)
		}
		clearString(&password)
	}

	logoutBtn.OnTapped = func() {
		pm.Logout()
		clearFieldsAndSelection()
		usernameLoginEntry.SetText("")
		passwordLoginEntry.SetText("")
		loginStatusLabel.SetText("")
		w.SetContent(loginContainer)
	}

	addBtn.OnTapped = func() {
		clearFieldsAndSelection()
		titleEntry.FocusGained()
		passwordEntryMain.Enable()
		saveBtn.Enable()
		addBtn.Disable()
	}

	saveBtn.OnTapped = func() {
		title := titleEntry.Text
		entryUser := usernameEntryMain.Text
		password := passwordEntryMain.Text
		urlVal := urlEntry.Text
		notes := notesEntry.Text
		if title == "" {
			dialog.ShowError(fmt.Errorf("title cannot be empty"), w)
			return
		}
		var err error
		if selectedIndex == -1 {
			err = pm.AddEntry(title, entryUser, password, urlVal, notes)
			if err == nil {
				dialog.ShowInformation("Success", "Entry added successfully", w)
			}
		} else {
			err = pm.UpdateEntry(selectedIndex, title, entryUser, password, urlVal, notes)
			if err == nil {
				dialog.ShowInformation("Success", "Entry updated successfully", w)
			}
		}
		clearString(&password)
		if err != nil {
			dialog.ShowError(fmt.Errorf("failed to save entry: %w", err), w)
		} else {
			refreshListAndClear()
		}
	}

	deleteBtn.OnTapped = func() {
		if selectedIndex < 0 {
			dialog.ShowInformation("No Selection", "Please select an entry to delete.", w)
			return
		}
		if selectedIndex >= len(pm.Entries) {
			dialog.ShowError(fmt.Errorf("invalid selection index, please refresh"), w)
			refreshListAndClear()
			return
		}
		entryTitle := pm.Entries[selectedIndex].Title
		dialog.ShowConfirm("Confirm Delete", fmt.Sprintf("Are you sure you want to delete '%s'?", entryTitle), func(confirm bool) {
			if confirm {
				err := pm.DeleteEntry(selectedIndex)
				if err != nil {
					dialog.ShowError(fmt.Errorf("failed to delete entry: %w", err), w)
				} else {
					dialog.ShowInformation("Success", "Entry deleted successfully", w)
					refreshListAndClear()
				}
			}
		}, w)
	}

	viewPasswordBtn.OnTapped = func() {
		if selectedIndex < 0 {
			dialog.ShowInformation("No Selection", "Please select an entry to view its password.", w)
			return
		}
		if selectedIndex >= len(pm.Entries) {
			dialog.ShowError(fmt.Errorf("invalid selection index, please refresh"), w)
			refreshListAndClear()
			return
		}
		decryptedPassword, err := pm.GetDecryptedPassword(selectedIndex)
		if err != nil {
			dialog.ShowError(fmt.Errorf("could not decrypt password: %w", err), w)
			return
		}
		passwordDisplay := widget.NewLabel(decryptedPassword)
		passwordDisplay.TextStyle.Monospace = true
		dialog.ShowCustomConfirm(
			"Decrypted Password", "OK", "Copy",
			container.NewVBox(passwordDisplay),
			func(copy bool) {
				if copy {
					w.Clipboard().SetContent(decryptedPassword)
					go func(pwdToClear string) {
						time.Sleep(30 * time.Second)
						currentContent := w.Clipboard().Content()
						if currentContent == pwdToClear {
							w.Clipboard().SetContent("")
						}
						clearString(&pwdToClear)
					}(decryptedPassword)
				}
				clearString(&decryptedPassword)
			},
			w,
		)
	}

	generatePasswordBtn.OnTapped = func() {
		length := 16
		_, err := fmt.Sscan(lengthEntry.Text, &length)
		if err != nil || length <= 0 {
			length = 16
			lengthEntry.SetText("16")
			dialog.ShowInformation("Invalid Length", "Using default length of 16.", w)
		}
		password, err := GeneratePassword(
			length,
			useUppercaseCheck.Checked,
			useLowercaseCheck.Checked,
			useNumbersCheck.Checked,
			useSpecialCheck.Checked,
		)
		if err != nil {
			dialog.ShowError(err, w)
			generatedPasswordEntry.SetText("")
			copyGeneratedBtn.Disable()
			return
		}
		generatedPasswordEntry.SetText(password)
		copyGeneratedBtn.Enable()
	}

	clearFormBtn.OnTapped = func() {
		clearFieldsAndSelection()
	}

	entriesList.OnSelected = func(id widget.ListItemID) {
		entries := pm.GetEntries()
		if id < 0 || id >= len(entries) {
			clearFieldsAndSelection()
			return
		}
		entry := entries[id]
		selectedIndex = id
		titleEntry.SetText(entry.Title)
		usernameEntryMain.SetText(entry.Username)
		passwordEntryMain.SetText("")
		passwordEntryMain.SetPlaceHolder("*** ENCRYPTED ***")
		passwordEntryMain.Disable()
		urlEntry.SetText(entry.URL)
		notesEntry.SetText(entry.Notes)
		saveBtn.Enable()
		deleteBtn.Enable()
		viewPasswordBtn.Enable()
		addBtn.Disable()
	}

	entriesList.OnUnselected = func(id widget.ListItemID) {
		if selectedIndex == id {
			clearFieldsAndSelection()
		}
	}

	clearFieldsAndSelection()
	w.SetContent(loginContainer)
	w.SetCloseIntercept(func() {
		if pm.LoggedIn {
			pm.Logout()
		}
		w.Close()
	})
	w.ShowAndRun()
	if pm.LoggedIn {
		pm.Logout()
	}
	fmt.Println("Application closed.")
}

// --- CLI Version (Commented out scanner initialization as it's unused) ---
func runCLI() {
	pm := NewPasswordManager()
	// scanner := bufio.NewScanner(os.Stdin) // Commented out to resolve unused variable error

	defer func() { // Ensure logout on CLI exit
		if pm.LoggedIn {
			pm.Logout()
			fmt.Println("\nLogged out, sensitive data cleared.")
		}
	}()

	// ... (CLI code remains largely the same for structure, but calls to Encrypt/Decrypt
	// would need updating if this part was to be fully functional with the new crypto) ...
	// For example, in "Add Entry":
	// password := scanner.Text()
	// err := pm.AddEntry(title, username, password, url, notes) // AddEntry now handles new encryption
	//
	// And in "View Entry Details":
	// decryptedPassword, err := pm.GetDecryptedPassword(index - 1) // GetDecryptedPassword handles new decryption

	// For brevity, the detailed CLI updates for new encryption are omitted here,
	// but the GUI main function shows how AddEntry and GetDecryptedPassword are used.
	// The principles would be the same for the CLI.

	fmt.Println("CLI mode needs updates for the new encryption scheme.")
	fmt.Println("Please run the GUI version (default).")

}
