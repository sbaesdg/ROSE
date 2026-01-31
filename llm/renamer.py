from custom_logger import logger

class Renamer:
    def __init__(self):
        self.rename_old_to_new = {}
        self.rename_new_to_old = {}
        self.special_token_map = {
            "->": "__TO__"
        }

    def add_rename(self, old_name, new_name):
        if old_name in self.rename_old_to_new:
            logger.warning(f"Old name {old_name} already exists, overwriting")
        if new_name in self.rename_new_to_old:
            logger.warning(f"New name {new_name} already exists, overwriting")
        self.rename_old_to_new[old_name] = new_name
        self.rename_new_to_old[new_name] = old_name
        logger.info(f"Renamed {old_name} to {new_name}")

    def get_new_name(self, old_name):
        assert old_name in self.rename_old_to_new, f"Old name {old_name} not found"
        return self.rename_old_to_new[old_name]

    def get_old_name(self, new_name):
        assert new_name in self.rename_new_to_old, f"New name {new_name} not found"
        return self.rename_new_to_old[new_name]

    def scrutinize_str(self, s: str) -> str:
        for token, replacement in self.special_token_map.items():
            s = s.replace(token, replacement)
        return s

    def descrutinize_str(self, s: str) -> str:
        for token, replacement in self.special_token_map.items():
            s = s.replace(replacement, token)
        return s

    def scrutinize_var_name(self, s: str) -> str:
        return self.scrutinize_str(s)

    def descrutinize_var_name(self, s: str) -> str:
        return self.descrutinize_str(s)
    
    def get_last_field(self, s: str) -> str:
        # bsdtar->extract_flags -> extract_flags
        # bsdtar__TO__extract_flags -> extract_flags
        s = self.scrutinize_var_name(s)
        parts = s.split("__TO__")
        assert len(parts) >= 1, f"Invalid variable name format: {s}"
        return parts[-1]
    
    def scrutinize_field(self, constraint):
        special_tokens = ["__TO__", "->"]
        for token in special_tokens:
            all_positions = []
            start = 0
            while True:
                start = constraint.find(token, start)
                if start == -1:
                    break
                all_positions.append(start)
                start += len(token)
            name_mapping = {}
            for pos in all_positions:
                # find the start and end of the variable name
                left = pos - 1
                while left >= 0 and constraint[left] not in [' ', '(', '[', '{', '=', '!', '&', '|', '>', '<', '+', '-', '*', '/', '%', '^']:
                    left -= 1
                left += 1
                right = pos + len(token)
                while right < len(constraint) and constraint[right] not in [' ', '(', '[', '{', '=', '!', '&', '|', '>', '<', '+', '-', '*', '/', '%', '^']:
                    right += 1
                full_var_name = constraint[left:right]
                last_field = self.get_last_field(full_var_name)
                name_mapping[full_var_name] = last_field
            # replace the variable names in the constraint
            for full_var_name, last_field in name_mapping.items():
                constraint = constraint.replace(full_var_name, last_field)
        return constraint