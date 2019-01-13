local trace = {}

function trace.handle(problem)
	local present = debug.getinfo(2)
	io.stderr:write(present.short_src .. ":" .. present.currentline .. ":\n")

	for i = 1, 255 do
		local info = {debug.getlocal(2, i)}
		if #info ~= 0 then
			local name, value = info[1], info[2]
			if name ~= "(*temporary)" then
				local lines = {}
				for line in (show(value) .. "\n"):gmatch "([^\n]*)\n" do
					table.insert(lines, line)
				end

				io.stderr:write("\t" .. name .. ":\n")
				local skipping = false
				for _, line in ipairs(lines) do
					if line:match "^\t\t" and 7 < #lines then
						if not skipping then
							io.stderr:write("\t\t\t\t...\n")
						end
						skipping = true
					else
						io.stderr:write("\t\t" .. line .. "\n")
						skipping = false
					end
				end
				io.stderr:write("\n\n")
			end
		end
	end

	io.stderr:write(debug.traceback())
	io.stderr:write("\n")
	return problem
end

-- RETURNS f(...)
function trace.run(f, ...)
	local a = {...}

	local function wrapped()
		return f(table.unpack(a))
	end

	local response = {xpcall(wrapped, trace.handle)}
	if not response[1] then
		io.stderr:write("\n")
		error(response[2])
	end

	return table.unpack(response, 2)
end

do
	local a = trace.run(function(a) return a + 1 end, 1)
	assert(a == 2, "expected `2` but got `" .. tostring(a) .. "`")
end

return trace
