
# 🌐 Генератор уязвимых Bitcoin-адресов и Проверка Баланса 1.2

Этот проект на C++ предназначен для генерации Bitcoin-адресов, проверки их балансов с использованием API Blockchain.info и сохранения данных в базе данных SQLite. Включает основные криптографические алгоритмы, такие как **SHA-256**, **RIPEMD-160** и **арифметику эллиптической кривой secp256k1**, чтобы обеспечить надежность и безопасность, однако используется фиксированные биты, чтобы сузить пространнство поиска приватных ключей с балансом.

---

## 🚀 Возможности

- 🔐 **Криптография на эллиптических кривых (secp256k1)**: Полная реализация арифметики точек кривой.
- 🔑 **Генерация Bitcoin-адресов**: Применение хеширования и кодирования Base58Check для создания уникальных адресов.
- 📊 **Проверка балансов**: Интеграция с API Blockchain.info для получения актуальной информации.
- 🗃️ **Интеграция с SQLite**: Сохранение приватных ключей, адресов и балансов.
- ⚡ **Обработка в пакетах**: Генерация и обработка адресов батчами для повышения эффективности.
- 🌐 **Работа с HTTP через CURL**: Удобная обработка запросов и JSON-ответов.

---

## 📚 Как это работает

1. **Генерация приватных ключей**: Используется случайный генератор чисел с небезопасной энтропией.
2. **Вычисление публичных ключей**: Используется арифметика эллиптической кривой secp256k1.
3. **Создание Bitcoin-адресов**:
   - Применяется SHA-256 к публичному ключу.
   - Полученный результат хешируется через RIPEMD-160.
   - Хеш кодируется в формате Base58Check.
4. **Проверка балансов**: Используется API Blockchain.info для получения информации о балансе.
5. **Сохранение данных**: Приватные ключи, адреса и балансы сохраняются в SQLite базу.

---



## 📊 Пример вывода

```plaintext
Address: 1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa Balance: 0 PrivKey(hex): 1ef3ab27f4...
Address: 1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2 Balance: 0.005 BTC PrivKey(hex): 3e89f5c4...
```

---

## 🔧 Основные компоненты

1. **Криптографические алгоритмы**: Реализованы SHA-256 и RIPEMD-160. Работа с эллиптической кривой secp256k1, включая умножение точек.
2. **SQLite**: Создание таблиц для хранения ключей, адресов и балансов. Добавление и обновление записей через SQL-запросы.
3. **HTTP-запросы**: Использование CURL для взаимодействия с Blockchain.info. Обработка JSON-ответов с помощью `nlohmann/json`.
4. **Base58Check**: Преобразование хешированных данных в формат Bitcoin-адреса.

---

## 🤔 Возможные улучшения

- **Поддержка дополнительных API для проверки балансов.**
- **Ускорение генерации адресов с помощью многопоточности.**
- **Добавление форматов адресов SegWit и Bech32.**

---

## ⚠️ Предупреждение

Этот проект предназначен исключительно для образовательных целей. **Не используйте его в незаконных или вредоносных целях.** Автор не несет ответственности за возможное нарушение законов.

## 🚀 Поддержать проект
- TON: UQCdINNjebB9Xe_CQSUEVQ44OTtRBQkh2jIOAcMX3e1qhIDb
- BTC: 1HahmL9iZQ1HwUp9iTqEuEbJT5HhRiiM81
- USDT TRC20: TG1MQa8ZpEJYwFaYSx2jNNotyq6e3g87in 
---
## ⚠️ Версия 1.2
- Реализована механика парсинга ответа от API
- Реализована маханика генерации по фиксированным битам приватного ключа, что гарантирует слабый (уязвимый паттерн)
- Обновлена функция записи в бд
---


